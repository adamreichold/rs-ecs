use std::any::TypeId;
use std::collections::HashMap;
use std::convert::TryInto;
use std::hash::{BuildHasherDefault, Hasher};
use std::num::NonZeroU32;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::archetype::{Archetype, Comp, CompMut, TypeMetadataSet};

/// The world storing entities and their components.
pub struct World {
    tag: u32,
    pub(crate) entities: Vec<EntityMetadata>,
    free_list: Vec<u32>,
    pub(crate) archetypes: Vec<Archetype>,
    insert_map: IndexTypeIdMap<u16>,
    remove_map: IndexTypeIdMap<u16>,
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

        Self {
            tag: tag(),
            entities: Default::default(),
            free_list: Default::default(),
            archetypes: vec![Archetype::new(empty_archetype)],
            insert_map: Default::default(),
            remove_map: Default::default(),
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

        meta.ty = 0;
        meta.idx = unsafe { self.archetypes[0].alloc() };

        let ent = Entity { id, gen: meta.gen };

        unsafe {
            self.archetypes[0].pointer::<Entity>(meta.idx).write(ent);
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
                let swapped_ent = archetype.pointer::<Entity>(idx).read();

                entities[swapped_ent.id as usize].idx = idx;
            }
        }
    }

    /// Remove all entites and their components from the world.
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
    /// # Panics
    ///
    /// Panics if one of the components is already present for the entity.
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
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        let key = TypeId::of::<B>();

        let new_ty = if let Some(ty) = self.insert_map.get(&(meta.ty, key)) {
            *ty
        } else {
            Self::insert_cold(
                &mut self.archetypes,
                &mut self.insert_map,
                &mut self.remove_map,
                key,
                B::insert,
                meta.ty,
            )
        };

        let old_ty = meta.ty;
        let old_idx = meta.idx;

        unsafe {
            let new_idx = self.move_(ent.id, old_ty, new_ty, old_idx);

            comps.write(&mut self.archetypes[new_ty as usize], new_idx);
        }
    }

    #[cold]
    #[inline(never)]
    fn insert_cold(
        archetypes: &mut Vec<Archetype>,
        insert_map: &mut IndexTypeIdMap<u16>,
        remove_map: &mut IndexTypeIdMap<u16>,
        key: TypeId,
        insert: fn(&mut TypeMetadataSet),
        old_ty: u16,
    ) -> u16 {
        let mut types = archetypes[old_ty as usize].types();
        insert(&mut types);

        let new_ty = Self::get_or_insert(archetypes, types);

        insert_map.insert((old_ty, key), new_ty);
        remove_map.insert((new_ty, key), old_ty);

        new_ty
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
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        let key = TypeId::of::<B>();

        let new_ty = if let Some(ty) = self.remove_map.get(&(meta.ty, key)) {
            *ty
        } else {
            Self::remove_cold(
                &mut self.archetypes,
                &mut self.insert_map,
                &mut self.remove_map,
                key,
                B::remove,
                meta.ty,
            )?
        };

        let old_ty = meta.ty;
        let old_idx = meta.idx;

        unsafe {
            let comps = B::read(&mut self.archetypes[old_ty as usize], old_idx);

            self.move_(ent.id, old_ty, new_ty, old_idx);

            Some(comps)
        }
    }

    #[cold]
    #[inline(never)]
    fn remove_cold(
        archetypes: &mut Vec<Archetype>,
        insert_map: &mut IndexTypeIdMap<u16>,
        remove_map: &mut IndexTypeIdMap<u16>,
        key: TypeId,
        remove: fn(&mut TypeMetadataSet) -> Option<()>,
        old_ty: u16,
    ) -> Option<u16> {
        let mut types = archetypes[old_ty as usize].types();
        remove(&mut types)?;

        let new_ty = Self::get_or_insert(archetypes, types);

        remove_map.insert((old_ty, key), new_ty);
        insert_map.insert((new_ty, key), old_ty);

        Some(new_ty)
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
            let old_comps = B1::read(&mut self.archetypes[old_ty as usize], old_idx);

            let new_idx = if new_ty != old_ty {
                self.move_(ent.id, old_ty, new_ty, old_idx)
            } else {
                old_idx
            };

            new_comps.write(&mut self.archetypes[new_ty as usize], new_idx);

            Some(old_comps)
        }
    }

    #[cold]
    #[inline(never)]
    fn exchange_cold(
        archetypes: &mut Vec<Archetype>,
        exchange_map: &mut IndexTypeIdMap<u16>,
        key: TypeId,
        remove: fn(&mut TypeMetadataSet) -> Option<()>,
        insert: fn(&mut TypeMetadataSet),
        old_ty: u16,
    ) -> Option<u16> {
        let mut types = archetypes[old_ty as usize].types();
        remove(&mut types)?;
        insert(&mut types);

        let new_ty = Self::get_or_insert(archetypes, types);

        exchange_map.insert((old_ty, key), new_ty);

        Some(new_ty)
    }

    fn get_or_insert(archetypes: &mut Vec<Archetype>, types: TypeMetadataSet) -> u16 {
        let pos = archetypes
            .iter_mut()
            .position(|archetype| archetype.match_(&types));

        if let Some(pos) = pos {
            pos as u16
        } else {
            let len = archetypes.len();
            assert!(len < u16::MAX as usize);

            archetypes.push(Archetype::new(types));

            len as u16
        }
    }

    unsafe fn move_(&mut self, id: u32, old_ty: u16, new_ty: u16, old_idx: u32) -> u32 {
        debug_assert_ne!(old_ty, new_ty);

        let old_archetype = &mut *self.archetypes.as_mut_ptr().add(old_ty as usize);
        let new_archetype = &mut *self.archetypes.as_mut_ptr().add(new_ty as usize);

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
    /// let comp = another_world.get::<String>(entity).unwrap();
    /// assert_eq!(&*comp, "Goodbye");
    /// ```
    pub fn transfer(&mut self, ent: Entity, other: &mut World) -> Entity {
        let meta = &mut self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        // allocate entity in other
        let id = other.alloc_id();

        let new_meta = &mut other.entities[id as usize];

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
            id,
            gen: new_meta.gen,
        };

        unsafe {
            other.archetypes[new_meta.ty as usize]
                .pointer::<Entity>(new_meta.idx)
                .write(ent);
        }

        ent
    }

    #[cold]
    #[inline(never)]
    fn transfer_cold(
        archetypes: &[Archetype],
        other_archetypes: &mut Vec<Archetype>,
        transfer_map: &mut IndexTagMap<u16>,
        other_transfer_map: &mut IndexTagMap<u16>,
        tag: u32,
        other_tag: u32,
        old_ty: u16,
    ) -> u16 {
        let types = archetypes[old_ty as usize].types();

        let new_ty = Self::get_or_insert(other_archetypes, types);

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

    /// Get an immutable reference to the component of the given type for an [Entity].
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
    /// let comp = world.get::<u32>(entity).unwrap();
    /// ```
    pub fn get<C>(&self, ent: Entity) -> Option<Comp<'_, C>>
    where
        C: 'static,
    {
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        unsafe { self.archetypes[meta.ty as usize].get::<C>(meta.idx) }
    }

    /// Get a mutable reference to the component of the given type for an [Entity].
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
    /// let comp = world.get_mut::<u32>(entity).unwrap();
    /// ```
    pub fn get_mut<C>(&self, ent: Entity) -> Option<CompMut<'_, C>>
    where
        C: 'static,
    {
        assert_ne!(
            TypeId::of::<C>(),
            TypeId::of::<Entity>(),
            "Entity cannot be accessed mutably"
        );

        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        unsafe { self.archetypes[meta.ty as usize].get_mut::<C>(meta.idx) }
    }

    /// Either update or insert the value of component `C` at entity `ent`.
    ///
    /// # Example
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity1 = world.alloc();
    /// world.insert(entity1, (0,));
    ///
    /// let entity2 = world.alloc();
    ///
    /// world.upsert(entity1, 1);
    /// world.upsert(entity2, 2);
    /// ```
    pub fn upsert<C>(&mut self, ent: Entity, new_comp: C)
    where
        C: 'static,
    {
        if let Some(mut comp) = self.get_mut::<C>(ent) {
            *comp = new_comp;
            return;
        }

        self.insert(ent, (new_comp,));
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
        self.gen = unsafe { NonZeroU32::new_unchecked(self.gen.get().checked_add(1).unwrap()) };
    }
}

#[allow(clippy::missing_safety_doc)]
pub unsafe trait Bundle: 'static {
    fn insert(types: &mut TypeMetadataSet);
    #[must_use]
    fn remove(types: &mut TypeMetadataSet) -> Option<()>;
    unsafe fn write(self, archetype: &mut Archetype, idx: u32);
    unsafe fn read(archetype: &mut Archetype, idx: u32) -> Self;
}

macro_rules! impl_bundle_for_tuples {
    () => {};

    ($head:ident $(,$tail:ident)*) => {
        impl_bundle_for_tuples!($($tail),*);
        impl_bundle_for_tuples!(@impl $head $(,$tail)*);
    };

    (@impl $($types:ident),+) => {
        unsafe impl<$($types),+> Bundle for ($($types,)+)
        where
            $($types: 'static,)+
        {
            fn insert(types: &mut TypeMetadataSet) {
                $(types.insert::<$types>();)+
            }

            fn remove(types: &mut TypeMetadataSet) -> Option<()> {
                $(
                    assert_ne!(
                        TypeId::of::<$types>(),
                        TypeId::of::<Entity>(),
                        "Entity cannot be removed"
                    );

                    types.remove::<$types>()?;
                )+

                Some(())
            }

            #[allow(non_snake_case)]
            unsafe fn write(self, archetype: &mut Archetype, idx: u32) {
                let ($($types,)+) = self;
                $(archetype.pointer::<$types>(idx).write($types);)+
            }

            #[allow(non_snake_case)]
            unsafe fn read(archetype: &mut Archetype, idx: u32) -> Self {
                $(let $types = archetype.pointer::<$types>(idx).read();)+
                ($($types,)+)
            }
        }
    };
}

impl_bundle_for_tuples!(A, B, C, D, E, F, G, H, I, J);

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

    #[cfg(not(miri))]
    use std::hash::Hash;
    use std::mem::size_of;

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

        world.get::<Entity>(ent).unwrap();

        world.free(ent);

        world.get::<Entity>(ent).unwrap();
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

        assert_eq!(world.insert_map.len(), 0);
        assert_eq!(world.remove_map.len(), 0);

        let ent = world.alloc();

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 0);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 1);
        assert_eq!(world.archetypes[0].len(), 1);

        assert_eq!(world.insert_map.len(), 0);
        assert_eq!(world.remove_map.len(), 0);

        world.insert(ent, (23_i32,));

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 1);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 2);
        assert_eq!(world.archetypes[0].len(), 0);
        assert_eq!(world.archetypes[1].len(), 1);

        assert_eq!(world.insert_map.len(), 1);
        assert_eq!(world.insert_map[&(0, TypeId::of::<(i32,)>())], 1);

        assert_eq!(world.remove_map.len(), 1);
        assert_eq!(world.remove_map[&(1, TypeId::of::<(i32,)>())], 0);
    }

    #[test]
    fn removing_component_creates_archetype() {
        let mut world = World::new();

        assert_eq!(world.entities.len(), 0);

        assert_eq!(world.archetypes.len(), 1);
        assert_eq!(world.archetypes[0].len(), 0);

        assert_eq!(world.insert_map.len(), 0);
        assert_eq!(world.remove_map.len(), 0);

        let ent = world.alloc();

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 0);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 1);
        assert_eq!(world.archetypes[0].len(), 1);

        assert_eq!(world.insert_map.len(), 0);
        assert_eq!(world.remove_map.len(), 0);

        world.insert(ent, (23_i32, 42_u64));

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 1);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 2);
        assert_eq!(world.archetypes[0].len(), 0);
        assert_eq!(world.archetypes[1].len(), 1);

        assert_eq!(world.insert_map.len(), 1);
        assert_eq!(world.insert_map[&(0, TypeId::of::<(i32, u64)>())], 1);

        assert_eq!(world.remove_map.len(), 1);
        assert_eq!(world.remove_map[&(1, TypeId::of::<(i32, u64)>())], 0);

        world.remove::<(i32,)>(ent).unwrap();

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen.get(), 1);
        assert_eq!(world.entities[0].ty, 2);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 3);
        assert_eq!(world.archetypes[0].len(), 0);
        assert_eq!(world.archetypes[1].len(), 0);
        assert_eq!(world.archetypes[2].len(), 1);

        assert_eq!(world.insert_map.len(), 2);
        assert_eq!(world.insert_map[&(0, TypeId::of::<(i32, u64)>())], 1);
        assert_eq!(world.insert_map[&(2, TypeId::of::<(i32,)>())], 1);

        assert_eq!(world.remove_map.len(), 2);
        assert_eq!(world.remove_map[&(1, TypeId::of::<(i32, u64)>())], 0);
        assert_eq!(world.remove_map[&(1, TypeId::of::<(i32,)>())], 2);
    }

    #[test]
    fn trival_exchange_does_not_create_aliasing_unique_references() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, (true,));

        world.exchange::<(bool,), _>(ent, (false,)).unwrap();

        assert_eq!(world.exchange_map.len(), 1);
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

        let comp = world.get::<i32>(ent).unwrap();
        assert_eq!(*comp, 23);
    }

    #[test]
    fn get_mut_then_get() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, (23,));

        {
            let mut comp = world.get_mut::<i32>(ent).unwrap();
            *comp = 42;
        }

        let comp = world.get::<i32>(ent).unwrap();
        assert_eq!(*comp, 42);
    }

    #[test]
    fn borrows_can_be_shared() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, ((),));

        let _comp = world.get::<()>(ent).unwrap();
        let _comp = world.get::<()>(ent).unwrap();
    }

    #[test]
    #[should_panic]
    fn mutable_borrows_are_exclusive() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, ((),));

        let _comp = world.get_mut::<()>(ent);
        let _comp = world.get_mut::<()>(ent).unwrap();
    }

    #[test]
    fn entity_id_are_consistent() {
        let mut world = World::new();

        let ent1 = world.alloc();
        let ent2 = world.alloc();
        world.free(ent1);
        let ent3 = world.alloc();

        assert_eq!(*world.get::<Entity>(ent2).unwrap(), ent2);
        assert_eq!(*world.get::<Entity>(ent3).unwrap(), ent3);
    }

    #[test]
    #[should_panic]
    fn entity_id_cannot_be_modified() {
        let mut world = World::new();

        let ent = world.alloc();
        let _ = world.get_mut::<Entity>(ent);
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

        let comp = world2.get::<i32>(ent2).unwrap();
        assert_eq!(*comp, 23);
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
