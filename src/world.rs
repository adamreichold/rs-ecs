use std::any::TypeId;
use std::collections::HashMap;
use std::convert::TryInto;
use std::hash::{BuildHasherDefault, Hasher};
use std::num::NonZeroU32;
use std::ops::BitXor;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::archetype::{Archetype, Comp, CompMut, TypeMetadataSet};

/// The ECS world storing [Entities](Entity) and components.
pub struct World {
    tag: u32,
    pub(crate) entities: Vec<EntityMetadata>,
    free_list: Vec<u32>,
    pub(crate) archetypes: Vec<Archetype>,
    insert_map: HashMap<(u32, TypeId), u32, BuildHasherDefault<IndexTypeIdHasher>>,
    remove_map: HashMap<(u32, TypeId), u32, BuildHasherDefault<IndexTypeIdHasher>>,
    move_into_map: HashMap<(u32, u32), u32, BuildHasherDefault<U32PairHasher>>,
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
            move_into_map: Default::default(),
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

        Self::free_idx(
            &mut self.archetypes[meta.ty as usize],
            meta.idx,
            true,
            &mut self.entities,
        );

        self.free_list.push(ent.id);
    }

    fn free_idx(archetype: &mut Archetype, idx: u32, drop: bool, entities: &mut [EntityMetadata]) {
        unsafe {
            if archetype.free(idx, drop) {
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
    pub(crate) fn tag_gen(&self) -> (u32, u32) {
        debug_assert!(!self.archetypes.is_empty());
        (self.tag, self.archetypes.len() as u32)
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

        let new_ty;

        if let Some(ty) = self.insert_map.get(&(meta.ty, TypeId::of::<B>())) {
            new_ty = *ty;
        } else {
            let mut types = self.archetypes[meta.ty as usize].types();
            B::insert(&mut types);

            new_ty = Self::get_or_insert(&mut self.archetypes, types);

            self.insert_map.insert((meta.ty, TypeId::of::<B>()), new_ty);
            self.remove_map.insert((new_ty, TypeId::of::<B>()), meta.ty);
        }

        let old_ty = meta.ty;
        let old_idx = meta.idx;

        unsafe {
            let new_idx = self.move_(ent.id, old_ty, new_ty, old_idx);

            comps.write(&mut self.archetypes[new_ty as usize], new_idx);
        }
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

        let new_ty;

        if let Some(ty) = self.remove_map.get(&(meta.ty, TypeId::of::<B>())) {
            new_ty = *ty;
        } else {
            let mut types = self.archetypes[meta.ty as usize].types();
            B::remove(&mut types)?;

            new_ty = Self::get_or_insert(&mut self.archetypes, types);

            self.remove_map.insert((meta.ty, TypeId::of::<B>()), new_ty);
            self.insert_map.insert((new_ty, TypeId::of::<B>()), meta.ty);
        }

        let old_ty = meta.ty;
        let old_idx = meta.idx;

        unsafe {
            let comps = B::read(&mut self.archetypes[old_ty as usize], old_idx);

            self.move_(ent.id, old_ty, new_ty, old_idx);

            Some(comps)
        }
    }

    fn get_or_insert(archetypes: &mut Vec<Archetype>, types: TypeMetadataSet) -> u32 {
        let pos = archetypes
            .iter_mut()
            .position(|archetype| archetype.match_(&types));

        if let Some(pos) = pos {
            pos as u32
        } else {
            let len = archetypes.len();
            assert!(len < u32::MAX as usize);

            archetypes.push(Archetype::new(types));

            len as u32
        }
    }

    unsafe fn move_(&mut self, id: u32, old_ty: u32, new_ty: u32, old_idx: u32) -> u32 {
        let old_archetype = &mut *self.archetypes.as_mut_ptr().add(old_ty as usize);
        let new_archetype = &mut *self.archetypes.as_mut_ptr().add(new_ty as usize);

        let new_idx = new_archetype.alloc();

        Archetype::move_(old_archetype, new_archetype, old_idx, new_idx);

        Self::free_idx(old_archetype, old_idx, false, &mut self.entities);

        let meta = &mut self.entities[id as usize];
        meta.ty = new_ty;
        meta.idx = new_idx;

        new_idx
    }
}

impl World {
    /// Move the components of an [Entity] from this world to another
    pub fn move_into(&mut self, ent: Entity, other: &mut World) -> Entity {
        let meta = &mut self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        // allocate entity in other
        let id = other.alloc_id();

        let new_meta = &mut other.entities[id as usize];

        // free entity in self
        meta.bump_gen();

        self.free_list.push(ent.id);

        // get or insert new archetype in other
        if let Some(ty) = self.move_into_map.get(&(meta.ty, other.tag)) {
            new_meta.ty = *ty;
        } else {
            let types = self.archetypes[meta.ty as usize].types();

            new_meta.ty = Self::get_or_insert(&mut other.archetypes, types);

            self.move_into_map.insert((meta.ty, other.tag), new_meta.ty);
            other.move_into_map.insert((new_meta.ty, self.tag), meta.ty);
        }

        // move components from old to new archetype
        let old_archetype = &mut self.archetypes[meta.ty as usize];
        let new_archetype = &mut other.archetypes[new_meta.ty as usize];

        unsafe {
            new_meta.idx = new_archetype.alloc();

            Archetype::move_(old_archetype, new_archetype, meta.idx, new_meta.idx);

            Self::free_idx(old_archetype, meta.idx, false, &mut self.entities);
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
        if TypeId::of::<C>() == TypeId::of::<Entity>() {
            panic!("Entity cannot be accessed mutably");
        }

        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        unsafe { self.archetypes[meta.ty as usize].get_mut::<C>(meta.idx) }
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
    pub ty: u32,
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
                    if TypeId::of::<$types>() == TypeId::of::<Entity>() {
                        panic!("Entity cannot be removed");
                    }

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

#[derive(Default)]
struct IndexTypeIdHasher(u64);

impl Hasher for IndexTypeIdHasher {
    fn write_u32(&mut self, val: u32) {
        self.0 = 1 + val as u64;
    }

    fn write_u64(&mut self, val: u64) {
        self.0 = self.0.wrapping_mul(val);
    }

    fn write(&mut self, _val: &[u8]) {
        unreachable!();
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

#[derive(Default)]
struct U32PairHasher(u64);

impl Hasher for U32PairHasher {
    fn write_u32(&mut self, val: u32) {
        const K: u64 = 0x517cc1b727220a95;

        self.0 = self.0.rotate_left(5).bitxor(val as u64).wrapping_mul(K);
    }

    fn write(&mut self, _val: &[u8]) {
        unreachable!();
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn adding_component_creates_archetype() {
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
    fn entities_can_be_moved_between_worlds() {
        let mut world1 = World::new();

        let ent1 = world1.alloc();
        world1.insert(ent1, (23, true, 42.0));
        world1.remove::<(bool,)>(ent1);

        let mut world2 = World::new();

        let ent2 = world1.move_into(ent1, &mut world2);

        assert_eq!(*world1.move_into_map.get(&(2, world2.tag)).unwrap(), 1);
        assert_eq!(*world2.move_into_map.get(&(1, world1.tag)).unwrap(), 2);

        assert!(!world1.exists(ent1));
        assert!(world2.exists(ent2));

        let comp = world2.get::<i32>(ent2).unwrap();
        assert_eq!(*comp, 23);
    }
}
