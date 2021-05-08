use std::any::TypeId;
use std::collections::HashMap;
use std::convert::TryInto;
use std::hash::{BuildHasherDefault, Hasher};
use std::sync::atomic::{AtomicU32, Ordering};

use crate::archetype::{Archetype, Comp, CompMut, TypeMetadataSet};

pub struct World {
    tag: u32,
    entities: Vec<EntityMetadata>,
    free_list: Vec<u32>,
    archetypes: Vec<Archetype>,
    insert_map: HashMap<(u32, TypeId), u32, BuildHasherDefault<IndexTypeIdHasher>>,
    remove_map: HashMap<(u32, TypeId), u32, BuildHasherDefault<IndexTypeIdHasher>>,
}

impl Default for World {
    fn default() -> Self {
        Self::new()
    }
}

impl World {
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
    #[must_use]
    pub fn alloc(&mut self) -> Entity {
        let id = if let Some(id) = self.free_list.pop() {
            id
        } else {
            let id = self.entities.len().try_into().unwrap();
            self.entities.push(Default::default());
            id
        };

        let meta = &mut self.entities[id as usize];

        meta.ty = 0;
        meta.idx = unsafe { self.archetypes[0].alloc() };

        let ent = Entity { id, gen: meta.gen };

        unsafe {
            self.archetypes[0].access::<Entity>(meta.idx).write(ent);
        }

        ent
    }

    pub fn free(&mut self, mut ent: Entity) {
        let meta = &mut self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen);

        meta.gen = meta.gen.checked_add(1).unwrap();
        ent.gen = meta.gen;

        let old_archetype = &mut self.archetypes[meta.ty as usize];

        unsafe {
            if old_archetype.free(meta.idx, true) {
                let moved_ent = old_archetype.access::<Entity>(meta.idx).read();

                self.entities[moved_ent.id as usize].idx = meta.idx;
            }
        }

        self.free_list.push(ent.id);
    }
}

impl World {
    pub(crate) fn tag_gen(&self) -> (u32, u32) {
        debug_assert!(!self.archetypes.is_empty());
        (self.tag, self.archetypes.len() as u32)
    }

    pub(crate) fn archetypes(&self) -> &[Archetype] {
        &self.archetypes
    }

    pub fn insert<B>(&mut self, ent: Entity, comps: B)
    where
        B: Bundle,
    {
        let meta = self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen);

        let new_ty;

        if let Some(pos) = self.insert_map.get(&(meta.ty, TypeId::of::<B>())) {
            new_ty = *pos;
        } else {
            let mut types = self.archetypes[meta.ty as usize].types();
            B::insert(&mut types);

            new_ty = self.get_or_insert(types);

            self.insert_map.insert((meta.ty, TypeId::of::<B>()), new_ty);
            self.remove_map.insert((new_ty, TypeId::of::<B>()), meta.ty);
        }

        unsafe {
            let new_idx = self.move_(ent.id, meta.ty, new_ty, meta.idx);

            comps.write(&mut self.archetypes[new_ty as usize], new_idx);
        }
    }

    pub fn remove<B>(&mut self, ent: Entity) -> Option<B>
    where
        B: Bundle,
    {
        let meta = self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen);

        let new_ty;

        if let Some(pos) = self.remove_map.get(&(meta.ty, TypeId::of::<B>())) {
            new_ty = *pos;
        } else {
            let mut types = self.archetypes[meta.ty as usize].types();
            B::remove(&mut types)?;

            new_ty = self.get_or_insert(types);

            self.remove_map.insert((meta.ty, TypeId::of::<B>()), new_ty);
            self.insert_map.insert((new_ty, TypeId::of::<B>()), meta.ty);
        }

        unsafe {
            let comps = B::read(&mut self.archetypes[meta.ty as usize], meta.idx);

            self.move_(ent.id, meta.ty, new_ty, meta.idx);

            Some(comps)
        }
    }

    fn get_or_insert(&mut self, types: TypeMetadataSet) -> u32 {
        let pos = self
            .archetypes
            .iter_mut()
            .position(|archetype| archetype.match_(&types));

        if let Some(pos) = pos {
            pos as u32
        } else {
            let len = self.archetypes.len();
            assert!(len < u32::MAX as usize);

            self.archetypes.push(Archetype::new(types));

            len as u32
        }
    }

    unsafe fn move_(&mut self, id: u32, old_ty: u32, new_ty: u32, old_idx: u32) -> u32 {
        let old_archetype = &mut *self.archetypes.as_mut_ptr().add(old_ty as usize);
        let new_archetype = &mut *self.archetypes.as_mut_ptr().add(new_ty as usize);

        let new_idx = new_archetype.alloc();

        Archetype::move_(old_archetype, new_archetype, old_idx, new_idx);

        if old_archetype.free(old_idx, false) {
            let moved_ent = old_archetype.access::<Entity>(old_idx).read();

            self.entities[moved_ent.id as usize].idx = old_idx;
        }

        let meta = &mut self.entities[id as usize];
        meta.ty = new_ty;
        meta.idx = new_idx;

        new_idx
    }
}

impl World {
    pub fn contains<C>(&self, ent: Entity) -> bool
    where
        C: 'static,
    {
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen);

        self.archetypes[meta.ty as usize].find::<C>().is_some()
    }

    pub fn get<C>(&self, ent: Entity) -> Option<Comp<'_, C>>
    where
        C: 'static,
    {
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen);

        unsafe { self.archetypes[meta.ty as usize].get::<C>(meta.idx) }
    }

    pub fn get_mut<C>(&self, ent: Entity) -> Option<CompMut<'_, C>>
    where
        C: 'static,
    {
        if TypeId::of::<C>() == TypeId::of::<Entity>() {
            panic!("Entity cannot be accessed mutably");
        }

        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen);

        unsafe { self.archetypes[meta.ty as usize].get_mut::<C>(meta.idx) }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Entity {
    id: u32,
    gen: u32,
}

#[derive(Clone, Copy, Default)]
struct EntityMetadata {
    gen: u32,
    ty: u32,
    idx: u32,
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
                $(archetype.access::<$types>(idx).write($types);)+
            }

            #[allow(non_snake_case)]
            unsafe fn read(archetype: &mut Archetype, idx: u32) -> Self {
                $(let $types = archetype.access::<$types>(idx).read();)+
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

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(world.entities[0].gen, 0);
        assert_eq!(world.entities[0].ty, 0);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 1);
        assert_eq!(world.archetypes[0].len(), 1);

        assert_eq!(world.insert_map.len(), 0);
        assert_eq!(world.remove_map.len(), 0);

        world.insert(ent, (23_i32,));

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen, 0);
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
        assert_eq!(world.entities[0].gen, 0);
        assert_eq!(world.entities[0].ty, 0);
        assert_eq!(world.entities[0].idx, 0);

        assert_eq!(world.archetypes.len(), 1);
        assert_eq!(world.archetypes[0].len(), 1);

        assert_eq!(world.insert_map.len(), 0);
        assert_eq!(world.remove_map.len(), 0);

        world.insert(ent, (23_i32, 42_u64));

        assert_eq!(world.entities.len(), 1);
        assert_eq!(world.entities[0].gen, 0);
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
        assert_eq!(world.entities[0].gen, 0);
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
}
