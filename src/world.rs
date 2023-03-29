use std::any::TypeId;
use std::collections::HashMap;
use std::convert::TryInto;
use std::hash::{BuildHasherDefault, Hasher};
use std::mem::transmute_copy;
use std::num::NonZeroU32;
use std::process::abort;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::{
    archetype::{Archetype, Cloner, TypeMetadataSet},
    borrow_flags::BorrowFlags,
    query::{Fetch, FetchShared, QuerySpec},
};

/// The world storing entities and their components.
pub struct World {
    tag: u32,
    pub(crate) entities: Vec<EntityMetadata>,
    free_list: Vec<u32>,
    pub(crate) borrow_flags: BorrowFlags,
    pub(crate) archetypes: Vec<Archetype>,
    exchange_map: IndexTypeIdMap<u16>,
    transfer_map: IndexTagMap<u16>,
}

impl Default for World {
    /// Create an empty world.
    fn default() -> Self {
        Self::new()
    }
}

impl World {
    /// Create an empty world.
    pub fn new() -> Self {
        let mut empty_archetype = TypeMetadataSet::default();
        empty_archetype.insert::<Entity>();

        let mut borrow_flags = BorrowFlags::default();
        borrow_flags.insert(&empty_archetype);

        let archetypes = vec![Archetype::new(empty_archetype)];

        Self {
            tag: tag(),
            entities: Default::default(),
            free_list: Default::default(),
            borrow_flags,
            archetypes,
            exchange_map: Default::default(),
            transfer_map: Default::default(),
        }
    }
}

fn tag() -> u32 {
    static TAG: AtomicU32 = AtomicU32::new(0);

    TAG.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |tag| {
        tag.checked_add(1)
    })
    .unwrap()
}

impl World {
    /// Create an [Entity] without any components.
    /// To add components, see [Self::insert()].
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (42_u32, true));
    /// ```
    #[must_use]
    pub fn alloc(&mut self) -> Entity {
        let id = self.alloc_id();

        let meta = &mut self.entities[id as usize];
        let archetype = &mut self.archetypes[0];

        meta.ty = 0;
        meta.idx = unsafe { archetype.alloc() };

        let ent = Entity { id, gen: meta.gen };

        unsafe {
            archetype.get::<Entity>(meta.idx).write(ent);
        }

        ent
    }

    fn alloc_id(&mut self) -> u32 {
        if let Some(id) = self.free_list.pop() {
            id
        } else {
            let id = self.entities.len().try_into().unwrap();
            self.entities.push(Default::default());
            id
        }
    }

    /// Remove an [Entity] and all its components from the world.
    /// To remove components, see [Self::remove()].
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (42_u32, true));
    ///
    /// world.free(entity);
    /// ```
    pub fn free(&mut self, ent: Entity) {
        let meta = &mut self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        meta.bump_gen();

        Self::free_idx::<true>(
            &mut self.archetypes[meta.ty as usize],
            meta.idx,
            &mut self.entities,
        );

        self.free_list.push(ent.id);
    }

    fn free_idx<const DROP: bool>(
        archetype: &mut Archetype,
        idx: u32,
        entities: &mut [EntityMetadata],
    ) {
        unsafe {
            if archetype.free::<DROP>(idx) {
                let swapped_ent = archetype.get::<Entity>(idx).read();

                entities[swapped_ent.id as usize].idx = idx;
            }
        }
    }

    /// Remove all entites and their components from the world.
    ///
    /// Note that this will re-use the memory allocations but it will drop the meta-data
    /// which implies that previously used [`Entity`] values will be repeated.
    pub fn clear(&mut self) {
        self.entities.clear();
        self.free_list.clear();

        for archetype in &mut *self.archetypes {
            archetype.clear();
        }
    }
}

impl World {
    pub(crate) fn tag_gen(&self) -> (u32, u16) {
        debug_assert!(!self.archetypes.is_empty());
        (self.tag, self.archetypes.len() as u16)
    }

    /// Insert components for a given [Entity].
    ///
    /// If a component is already present for the entity, its value will be overwritten.
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (42_u32, true));
    /// world.insert(entity, (String::from("Hello"),));
    /// ```
    pub fn insert<B>(&mut self, ent: Entity, comps: B)
    where
        B: Bundle,
    {
        self.exchange::<(), B>(ent, comps);
    }

    /// Remove components for a given [Entity].
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (42_u32, true, String::from("Hello")));
    ///
    /// world.remove::<(u32, bool)>(entity).unwrap();
    /// world.remove::<(String,)>(entity).unwrap();
    /// ```
    pub fn remove<B>(&mut self, ent: Entity) -> Option<B>
    where
        B: Bundle,
    {
        self.exchange::<B, ()>(ent, ())
    }

    /// Exchange components for a given [Entity]
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (42_u32, true));
    /// assert!(world.contains::<u32>(entity));
    /// assert!(world.contains::<bool>(entity));
    /// assert!(!world.contains::<String>(entity));
    ///
    /// world.exchange::<(u32, bool), _>(entity, (String::from("Hello"),)).unwrap();
    /// assert!(!world.contains::<u32>(entity));
    /// assert!(!world.contains::<bool>(entity));
    /// assert!(world.contains::<String>(entity));
    /// ```
    pub fn exchange<B1, B2>(&mut self, ent: Entity, new_comps: B2) -> Option<B1>
    where
        B1: Bundle,
        B2: Bundle,
    {
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        let key = TypeId::of::<(B1, B2)>();

        let new_ty = if let Some(ty) = self.exchange_map.get(&(meta.ty, key)) {
            *ty
        } else {
            Self::exchange_cold(
                &mut self.archetypes,
                &mut self.borrow_flags,
                &mut self.exchange_map,
                key,
                B1::remove,
                B2::insert,
                meta.ty,
            )?
        };

        let old_ty = meta.ty;
        let old_idx = meta.idx;

        unsafe {
            let old_archetype = &mut self.archetypes[old_ty as usize];
            let old_comps = B1::read(old_archetype, old_idx);
            B2::drop::<B1>(old_archetype, old_idx);

            let new_idx = self.move_(ent.id, old_ty, new_ty, old_idx);

            let new_archetype = &mut self.archetypes[new_ty as usize];
            new_comps.write(new_archetype, new_idx);

            Some(old_comps)
        }
    }

    #[cold]
    #[inline(never)]
    fn exchange_cold(
        archetypes: &mut Vec<Archetype>,
        borrow_flags: &mut BorrowFlags,
        exchange_map: &mut IndexTypeIdMap<u16>,
        key: TypeId,
        remove: fn(&mut TypeMetadataSet) -> Option<()>,
        insert: fn(&mut TypeMetadataSet),
        old_ty: u16,
    ) -> Option<u16> {
        let mut types = archetypes[old_ty as usize].types();
        remove(&mut types)?;
        insert(&mut types);

        let new_ty = Self::get_or_insert(archetypes, borrow_flags, types);

        exchange_map.insert((old_ty, key), new_ty);

        Some(new_ty)
    }

    fn get_or_insert(
        archetypes: &mut Vec<Archetype>,
        borrow_flags: &mut BorrowFlags,
        types: TypeMetadataSet,
    ) -> u16 {
        let pos = archetypes
            .iter()
            .position(|archetype| archetype.match_(&types));

        if let Some(pos) = pos {
            pos as u16
        } else {
            let len = archetypes.len();
            assert!(len < u16::MAX as usize);

            borrow_flags.insert(&types);

            archetypes.push(Archetype::new(types));

            len as u16
        }
    }

    unsafe fn move_(&mut self, id: u32, old_ty: u16, new_ty: u16, old_idx: u32) -> u32 {
        if old_ty == new_ty {
            return old_idx;
        }

        debug_assert!(self.archetypes.len() > old_ty as usize);
        debug_assert!(self.archetypes.len() > new_ty as usize);

        let archetypes = self.archetypes.as_mut_ptr();
        let old_archetype = &mut *archetypes.add(old_ty as usize);
        let new_archetype = &mut *archetypes.add(new_ty as usize);

        let new_idx = new_archetype.alloc();

        Archetype::move_(old_archetype, new_archetype, old_idx, new_idx);

        Self::free_idx::<false>(old_archetype, old_idx, &mut self.entities);

        let meta = &mut self.entities[id as usize];
        meta.ty = new_ty;
        meta.idx = new_idx;

        new_idx
    }
}

impl World {
    /// Transfer an [Entity] and its components from this world to another.
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (23_i32, false, String::from("Goodbye")));
    ///
    /// let mut another_world = World::new();
    /// let entity = world.transfer(entity, &mut another_world);
    ///
    /// let comp = another_world.query_one::<&String>(entity).unwrap();
    /// assert_eq!(&*comp.get(), "Goodbye");
    /// ```
    pub fn transfer(&mut self, ent: Entity, other: &mut World) -> Entity {
        let meta = &mut self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        // allocate entity in other
        let new_id = other.alloc_id();

        let new_meta = &mut other.entities[new_id as usize];

        // free entity in self
        meta.bump_gen();

        self.free_list.push(ent.id);

        // get or insert new archetype in other
        new_meta.ty = if let Some(ty) = self.transfer_map.get(&(meta.ty, other.tag)) {
            *ty
        } else {
            Self::transfer_cold(
                &self.archetypes,
                &mut other.archetypes,
                &mut other.borrow_flags,
                &mut self.transfer_map,
                &mut other.transfer_map,
                self.tag,
                other.tag,
                meta.ty,
            )
        };

        // move components from old to new archetype
        let old_archetype = &mut self.archetypes[meta.ty as usize];
        let new_archetype = &mut other.archetypes[new_meta.ty as usize];

        unsafe {
            new_meta.idx = new_archetype.alloc();

            Archetype::move_(old_archetype, new_archetype, meta.idx, new_meta.idx);

            Self::free_idx::<false>(old_archetype, meta.idx, &mut self.entities);
        }

        // fix entity component in other
        let ent = Entity {
            id: new_id,
            gen: new_meta.gen,
        };

        unsafe {
            new_archetype.get::<Entity>(new_meta.idx).write(ent);
        }

        ent
    }

    #[allow(clippy::too_many_arguments)]
    #[cold]
    #[inline(never)]
    fn transfer_cold(
        archetypes: &[Archetype],
        other_archetypes: &mut Vec<Archetype>,
        other_borrows: &mut BorrowFlags,
        transfer_map: &mut IndexTagMap<u16>,
        other_transfer_map: &mut IndexTagMap<u16>,
        tag: u32,
        other_tag: u32,
        old_ty: u16,
    ) -> u16 {
        let types = archetypes[old_ty as usize].types();

        let new_ty = Self::get_or_insert(other_archetypes, other_borrows, types);

        transfer_map.insert((old_ty, other_tag), new_ty);
        other_transfer_map.insert((new_ty, tag), old_ty);

        new_ty
    }
}

impl World {
    /// Check if a given [Entity] exists.
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// assert!(world.exists(entity));
    ///
    /// world.free(entity);
    /// assert!(!world.exists(entity));
    /// ```
    pub fn exists(&self, ent: Entity) -> bool {
        let meta = &self.entities[ent.id as usize];
        ent.gen == meta.gen
    }

    /// Check if a certain component type is present for an [Entity].
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (42_u32, true));
    ///
    /// assert!(world.contains::<u32>(entity));
    /// ```
    pub fn contains<C>(&self, ent: Entity) -> bool
    where
        C: 'static,
    {
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        self.archetypes[meta.ty as usize].find::<C>().is_some()
    }

    /// Access the components matching given query for an [Entity].
    ///
    /// Note that for repeated calls, [map](crate::QueryRef::map) can be used to amortize the set-up costs.
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (42_u32, true));
    ///
    /// {
    ///     let mut comp = world.query_one::<&mut u32>(entity).unwrap();
    ///     *comp.get_mut() = 42;
    /// }
    ///
    /// let comp = world.query_one::<&u32>(entity).unwrap();
    /// assert_eq!(*comp.get(), 42);
    /// ```
    pub fn query_one<S>(&self, ent: Entity) -> Option<QueryOne<S>>
    where
        S: QuerySpec,
    {
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        let flags = S::Fetch::find_flags(&self.borrow_flags)?;
        let _ref = unsafe { S::Fetch::borrow(&self.borrow_flags, flags) };

        let archetype = &self.archetypes[meta.ty as usize];

        let comps = S::Fetch::find_comps(archetype)?;
        let ptr = unsafe { S::Fetch::base_pointer(archetype, comps) };

        Some(QueryOne {
            _ref,
            ptr,
            idx: meta.idx,
        })
    }
}

impl World {
    /// Creates a copy of the [`World`]
    ///
    /// This requires that all component types are available in the given [`cloner`][Cloner].
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let ent = world.alloc();
    /// world.insert(ent, (42, "foo".to_owned(),));
    ///
    /// let mut cloner = Cloner::new();
    ///
    /// cloner.add_copyable::<i32>();
    /// cloner.add_cloneable::<String>();
    ///
    /// let snapshot = world.clone(&cloner);
    ///
    /// let mut comp = world.query_one::<&mut String>(ent).unwrap();
    /// *comp.get_mut() = "bar".to_owned();
    ///
    /// let comp = snapshot.query_one::<&String>(ent).unwrap();
    /// assert_eq!(*comp.get(), "foo");
    /// ```
    pub fn clone(&mut self, cloner: &Cloner) -> Self {
        let archetypes = self
            .archetypes
            .iter_mut()
            .map(|archetype| archetype.clone(cloner))
            .collect();

        Self {
            tag: tag(),
            entities: self.entities.clone(),
            free_list: self.free_list.clone(),
            borrow_flags: self.borrow_flags.clone(),
            archetypes,
            exchange_map: self.exchange_map.clone(),
            transfer_map: self.transfer_map.clone(),
        }
    }
}

/// An opaque entity identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Entity {
    pub(crate) id: u32,
    pub(crate) gen: NonZeroU32,
}

#[derive(Clone, Copy)]
pub struct EntityMetadata {
    pub gen: NonZeroU32,
    pub ty: u16,
    pub idx: u32,
}

impl Default for EntityMetadata {
    fn default() -> Self {
        Self {
            gen: unsafe { NonZeroU32::new_unchecked(1) },
            ty: 0,
            idx: 0,
        }
    }
}

impl EntityMetadata {
    fn bump_gen(&mut self) {
        let gen = self.gen.get();

        if gen == u32::MAX {
            abort();
        }

        self.gen = unsafe { NonZeroU32::new_unchecked(gen + 1) };
    }
}

/// Query to access the specified components of a single entity.
pub struct QueryOne<'w, S>
where
    S: QuerySpec,
{
    _ref: <S::Fetch as Fetch<'w>>::Ref,
    ptr: <S::Fetch as Fetch<'w>>::Ptr,
    idx: u32,
}

impl<S> QueryOne<'_, S>
where
    S: QuerySpec,
{
    /// Gain shared access to the specified components.
    ///
    /// Available only if the components do not include unique references.
    pub fn get(&self) -> <S::Fetch as Fetch<'_>>::Item
    where
        S::Fetch: FetchShared,
    {
        unsafe { S::Fetch::deref(transmute_copy(&self.ptr), self.idx) }
    }

    /// Gain exclusive access to the specified components.
    pub fn get_mut(&mut self) -> <S::Fetch as Fetch<'_>>::Item {
        unsafe { S::Fetch::deref(transmute_copy(&self.ptr), self.idx) }
    }
}

#[allow(clippy::missing_safety_doc)]
pub unsafe trait Bundle
where
    Self: 'static,
{
    fn contains<T>() -> bool
    where
        T: 'static;

    fn insert(types: &mut TypeMetadataSet);
    #[must_use]
    fn remove(types: &mut TypeMetadataSet) -> Option<()>;

    unsafe fn drop<T>(archetype: &mut Archetype, idx: u32)
    where
        T: Bundle;

    unsafe fn write(self, archetype: &mut Archetype, idx: u32);
    unsafe fn read(archetype: &mut Archetype, idx: u32) -> Self;
}

macro_rules! impl_bundle_for_tuples {
    () => {
        impl_bundle_for_tuples!(@impl);
    };

    ($head:ident $(,$tail:ident)*) => {
        impl_bundle_for_tuples!($($tail),*);
        impl_bundle_for_tuples!(@rev $head $(,$tail)*;);
    };

    (@rev ; $($rev:ident),*) => {
        impl_bundle_for_tuples!(@impl $($rev),*);
    };

    (@rev $head:ident $(,$tail:ident)*; $($rev:ident),*) => {
        impl_bundle_for_tuples!(@rev $($tail),*; $head $(,$rev)*);
    };

    (@impl $($types:ident),*) => {
        #[allow(unused_variables)]
        unsafe impl<$($types),*> Bundle for ($($types,)*)
        where
            $($types: 'static,)*
        {
            fn contains<T>() -> bool
            where
                T: 'static
            {
                $(
                    if TypeId::of::<$types>() == TypeId::of::<T>() {
                        return true;
                    }
                )*

                false
            }

            fn insert(types: &mut TypeMetadataSet) {
                $(
                    assert_ne!(
                        TypeId::of::<$types>(),
                        TypeId::of::<Entity>(),
                        "Entity cannot be inserted"
                    );

                    types.insert::<$types>();
                )*
            }

            fn remove(types: &mut TypeMetadataSet) -> Option<()> {
                $(
                    assert_ne!(
                        TypeId::of::<$types>(),
                        TypeId::of::<Entity>(),
                        "Entity cannot be removed"
                    );

                    types.remove::<$types>()?;
                )*

                Some(())
            }

            unsafe fn drop<T>(archetype: &mut Archetype, idx: u32)
            where
                T: Bundle
            {
                $(
                    if !T::contains::<$types>() {
                        archetype.drop::<$types>(idx);
                    }
                )*
            }

            #[allow(non_snake_case)]
            unsafe fn write(self, archetype: &mut Archetype, idx: u32) {
                let ($($types,)*) = self;
                $(archetype.get::<$types>(idx).write($types);)*
            }

            #[allow(non_snake_case)]
            #[allow(clippy::unused_unit)]
            unsafe fn read(archetype: &mut Archetype, idx: u32) -> Self {
                $(let $types = archetype.get::<$types>(idx).read();)*
                ($($types,)*)
            }
        }
    };
}

impl_bundle_for_tuples!(J, I, H, G, F, E, D, C, B, A);

type IndexTypeIdMap<V> = HashMap<(u16, TypeId), V, BuildHasherDefault<IndexTypeIdHasher>>;

#[derive(Default)]
struct IndexTypeIdHasher(u64);

impl Hasher for IndexTypeIdHasher {
    fn write_u16(&mut self, val: u16) {
        self.0 = u64::from(val);
    }

    fn write_u64(&mut self, val: u64) {
        self.0 ^= val;
    }

    fn write(&mut self, _val: &[u8]) {
        unreachable!();
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

type IndexTagMap<V> = HashMap<(u16, u32), V, BuildHasherDefault<IndexTagHasher>>;

#[derive(Default)]
struct IndexTagHasher(u64);

impl Hasher for IndexTagHasher {
    fn write_u16(&mut self, val: u16) {
        self.0 = u64::from(val);
    }

    fn write_u32(&mut self, val: u32) {
        self.0 |= u64::from(val) << 16;
    }

    fn write(&mut self, _val: &[u8]) {
        unreachable!();
    }

    fn finish(&self) -> u64 {
        self.0.wrapping_mul(0x517cc1b727220a95)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::cell::Cell;
    #[cfg(not(miri))]
    use std::hash::Hash;
    use std::mem::size_of;
    use std::rc::Rc;

    struct SetOnDrop(Rc<Cell<bool>>);

    impl Drop for SetOnDrop {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }

    #[test]
    fn alloc_creates_unique_entities() {
        let mut world = World::new();

        let ent1 = world.alloc();
        let ent2 = world.alloc();

        world.free(ent1);
        let ent3 = world.alloc();

        assert_ne!(ent1, ent2);
        assert_ne!(ent2, ent3);

        assert_eq!(ent3.id, ent1.id);
        assert_ne!(ent3.gen, ent1.gen);
    }

    #[test]
    #[should_panic]
    fn freed_entities_cannot_be_accessed() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, (42,));

        world.query_one::<&i32>(ent).unwrap();

        world.free(ent);

        world.query_one::<&i32>(ent).unwrap();
    }

    #[test]
    fn entity_metadata_is_updated_after_compacting_archetypes() {
        let mut world = World::new();

        let ent1 = world.alloc();
        let _ent2 = world.alloc();
        let _ent3 = world.alloc();

        assert_eq!(world.entities.len(), 3);
        assert_eq!(world.entities[0].idx, 0);
        assert_eq!(world.entities[1].idx, 1);
        assert_eq!(world.entities[2].idx, 2);

        assert_eq!(world.free_list.len(), 0);

        world.free(ent1);

        assert_eq!(world.entities.len(), 3);
        assert_eq!(world.entities[1].idx, 1);
        assert_eq!(world.entities[2].idx, 0);

        assert_eq!(world.free_list.len(), 1);
        assert_eq!(world.free_list[0], 0);
    }

    #[test]
    fn inserting_component_creates_archetype() {
        let mut world = World::new();

        assert_eq!(world.entities.len(), 0);

        assert_eq!(world.archetypes.len(), 1);
        assert_eq!(world.archetypes[0].len(), 0);

        assert_eq!(world.exchange_map.len(), 0);

        let ent = world.alloc();

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 0);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 1);
        assert_eq!(world.archetypes[0].len(), 1);

        assert_eq!(world.exchange_map.len(), 0);

        world.insert(ent, (23_i32,));

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 1);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 2);
        assert_eq!(world.archetypes[0].len(), 0);
        assert_eq!(world.archetypes[1].len(), 1);

        assert_eq!(world.exchange_map.len(), 1);
        assert_eq!(world.exchange_map[&(0, TypeId::of::<((), (i32,))>())], 1);
    }

    #[test]
    fn removing_component_creates_archetype() {
        let mut world = World::new();

        assert_eq!(world.entities.len(), 0);

        assert_eq!(world.archetypes.len(), 1);
        assert_eq!(world.archetypes[0].len(), 0);

        assert_eq!(world.exchange_map.len(), 0);

        let ent = world.alloc();

        world.insert(ent, (23_i32, 42_u64));

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 1);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 2);
        assert_eq!(world.archetypes[0].len(), 0);
        assert_eq!(world.archetypes[1].len(), 1);

        assert_eq!(world.exchange_map.len(), 1);
        assert_eq!(
            world.exchange_map[&(0, TypeId::of::<((), (i32, u64))>())],
            1
        );

        world.remove::<(i32,)>(ent).unwrap();

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 2);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 3);
        assert_eq!(world.archetypes[0].len(), 0);
        assert_eq!(world.archetypes[1].len(), 0);
        assert_eq!(world.archetypes[2].len(), 1);

        assert_eq!(world.exchange_map.len(), 2);
        assert_eq!(
            world.exchange_map[&(0, TypeId::of::<((), (i32, u64))>())],
            1
        );
        assert_eq!(world.exchange_map[&(1, TypeId::of::<((i32,), ())>())], 2);
    }

    #[test]
    fn insert_can_be_used_to_overwrite_components() {
        let drop1 = Rc::new(Cell::new(false));
        let drop2 = Rc::new(Cell::new(false));
        let drop3 = Rc::new(Cell::new(false));

        let mut world = World::new();

        let entity1 = world.alloc();
        world.insert(entity1, (0, SetOnDrop(drop1.clone())));

        let entity2 = world.alloc();

        world.insert(entity1, (1, SetOnDrop(drop2.clone())));
        world.insert(entity2, (2, SetOnDrop(drop3.clone())));

        assert_eq!(*world.query_one::<&i32>(entity1).unwrap().get(), 1);
        assert_eq!(*world.query_one::<&i32>(entity2).unwrap().get(), 2);

        assert_eq!(world.exchange_map.len(), 2);
        assert_eq!(
            world.exchange_map[&(0, TypeId::of::<((), (i32, SetOnDrop))>())],
            1
        );
        assert_eq!(
            world.exchange_map[&(1, TypeId::of::<((), (i32, SetOnDrop))>())],
            1
        );

        assert!(drop1.get());
        assert!(!drop2.get());
        assert!(!drop3.get());
    }

    #[test]
    fn exchange_can_be_used_to_overwrite_components() {
        let drop1 = Rc::new(Cell::new(false));
        let drop2 = Rc::new(Cell::new(false));

        let mut world = World::new();

        let entity = world.alloc();
        world.insert(entity, (0, true, SetOnDrop(drop1.clone())));
        world
            .exchange::<(bool,), _>(entity, (1, SetOnDrop(drop2.clone())))
            .unwrap();

        assert_eq!(*world.query_one::<&i32>(entity).unwrap().get(), 1);
        assert!(!world.contains::<bool>(entity));

        assert_eq!(world.exchange_map.len(), 2);
        assert_eq!(
            world.exchange_map[&(0, TypeId::of::<((), (i32, bool, SetOnDrop))>())],
            1
        );
        assert_eq!(
            world.exchange_map[&(1, TypeId::of::<((bool,), (i32, SetOnDrop))>())],
            2
        );

        assert!(drop1.get());
        assert!(!drop2.get());
    }

    #[test]
    #[allow(clippy::let_unit_value)]
    fn empty_remove_is_essentially_a_noop() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, (true,));

        let () = world.remove::<()>(ent).unwrap();
    }

    #[test]
    fn trival_exchange_does_not_create_aliasing_unique_references() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, (true,));

        world.exchange::<(bool,), _>(ent, (false,)).unwrap();

        assert_eq!(world.exchange_map.len(), 2);
        assert_eq!(world.exchange_map[&(0, TypeId::of::<((), (bool,))>())], 1);
        assert_eq!(
            world.exchange_map[&(1, TypeId::of::<((bool,), (bool,))>())],
            1
        );
    }

    #[test]
    fn insert_then_get() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, (23,));

        let comp = world.query_one::<&i32>(ent).unwrap();
        assert_eq!(*comp.get(), 23);
    }

    #[test]
    fn get_mut_then_get() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, (23,));

        {
            let mut comp = world.query_one::<&mut i32>(ent).unwrap();
            *comp.get_mut() = 42;
        }

        let comp = world.query_one::<&i32>(ent).unwrap();
        assert_eq!(*comp.get(), 42);
    }

    #[test]
    fn borrows_can_be_shared() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, ((),));

        let _comp = world.query_one::<&()>(ent).unwrap();
        let _comp = world.query_one::<&()>(ent).unwrap();
    }

    #[test]
    #[should_panic]
    fn mutable_borrows_are_exclusive() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, ((),));

        let _comp = world.query_one::<&mut ()>(ent).unwrap();
        let _comp = world.query_one::<&mut ()>(ent).unwrap();
    }

    #[test]
    fn entity_id_are_consistent() {
        let mut world = World::new();

        let ent1 = world.alloc();
        let ent2 = world.alloc();
        world.free(ent1);
        let ent3 = world.alloc();

        assert_eq!(*world.query_one::<&Entity>(ent2).unwrap().get(), ent2);
        assert_eq!(*world.query_one::<&Entity>(ent3).unwrap().get(), ent3);
    }

    #[test]
    #[should_panic]
    fn entity_id_cannot_be_modified() {
        let mut world = World::new();

        let ent = world.alloc();
        let _ = world.query_one::<&mut Entity>(ent);
    }

    #[test]
    #[should_panic]
    fn entity_id_cannot_be_removed() {
        let mut world = World::new();

        let ent = world.alloc();
        let _ = world.remove::<(Entity,)>(ent);
    }

    #[test]
    fn entity_has_niche() {
        assert_eq!(size_of::<Entity>(), size_of::<Option<Entity>>());
    }

    #[test]
    fn world_can_be_cleared() {
        let mut world = World::new();

        let ent1 = world.alloc();
        world.insert(ent1, (23,));

        let ent2 = world.alloc();
        world.free(ent2);

        assert_eq!(world.entities.len(), 2);
        assert_eq!(world.free_list.len(), 1);

        assert_eq!(world.archetypes.len(), 2);
        assert_eq!(world.archetypes[0].len(), 0);
        assert_eq!(world.archetypes[1].len(), 1);

        world.clear();

        assert_eq!(world.entities.len(), 0);
        assert_eq!(world.free_list.len(), 0);

        assert_eq!(world.archetypes.len(), 2);
        assert_eq!(world.archetypes[0].len(), 0);
        assert_eq!(world.archetypes[1].len(), 0);
    }

    #[test]
    fn clearing_the_world_repeats_entities() {
        let mut world = World::new();

        let ent = world.alloc();
        assert_eq!(ent.id, 0);
        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);

        world.clear();

        let ent = world.alloc();
        assert_eq!(ent.id, 0);
        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
    }

    #[test]
    fn entities_can_be_transferred_between_worlds() {
        let mut world1 = World::new();

        let ent1 = world1.alloc();
        world1.insert(ent1, (23, true, 42.0));
        world1.remove::<(bool,)>(ent1);

        let mut world2 = World::new();

        let ent2 = world1.transfer(ent1, &mut world2);

        assert_eq!(*world1.transfer_map.get(&(2, world2.tag)).unwrap(), 1);
        assert_eq!(*world2.transfer_map.get(&(1, world1.tag)).unwrap(), 2);

        assert!(!world1.exists(ent1));
        assert!(world2.exists(ent2));

        let comp = world2.query_one::<&i32>(ent2).unwrap();
        assert_eq!(*comp.get(), 23);
    }

    #[test]
    fn worlds_can_be_cloned() {
        let mut world1 = World::new();

        let ent = world1.alloc();
        world1.insert(ent, (23, true, 42.0));
        world1.insert(ent, ("foobar".to_owned(),));

        let mut cloner = Cloner::new();

        cloner.add_copyable::<i32>();
        cloner.add_copyable::<bool>();
        cloner.add_copyable::<f64>();
        cloner.add_cloneable::<String>();

        let world2 = world1.clone(&cloner);

        assert!(world1.exists(ent));
        assert!(world2.exists(ent));

        let comp = world2.query_one::<&String>(ent).unwrap();
        assert_eq!(*comp.get(), "foobar");
    }

    #[cfg(not(miri))]
    #[test]
    fn index_type_id_yields_uniformly_distributed_lower_bits() {
        let mut histogram = [0; 128];

        for i in 0_u16..1024 {
            for t in [
                TypeId::of::<(i32,)>(),
                TypeId::of::<(bool, f32)>(),
                TypeId::of::<(i32, &str)>(),
                TypeId::of::<(bool, &str, f64)>(),
            ] {
                let mut hasher = IndexTypeIdHasher::default();
                (i, t).hash(&mut hasher);
                let hash = hasher.finish();

                histogram[hash as usize % histogram.len()] += 1;
            }
        }

        for count in histogram {
            assert_eq!(count, 1024 * 4 / histogram.len());
        }
    }

    #[cfg(not(miri))]
    #[test]
    fn index_tag_hasher_yields_uniformly_distributed_lower_bits() {
        let mut histogram = [0; 128];

        for i in 0_u16..1024 {
            for j in 0_u32..128 {
                let mut hasher = IndexTagHasher::default();
                (i, j).hash(&mut hasher);
                let hash = hasher.finish();

                histogram[hash as usize % histogram.len()] += 1;
            }
        }

        for count in histogram {
            assert_eq!(count, 1024 * 128 / histogram.len());
        }
    }
}
