use std::any::TypeId;
use std::collections::HashMap;
use std::convert::TryInto;

use crate::{
    archetype::{Archetype, Comp, CompMut, TypeMetadata},
    resources::{Res, ResMut, Resources},
};

pub struct World {
    entities: Vec<EntityMetadata>,
    free_list: Vec<u32>,
    archetypes: Vec<Archetype>,
    insert_map: HashMap<(u32, TypeId), u32>,
    remove_map: HashMap<(u32, TypeId), u32>,
    resources: Resources,
}

impl Default for World {
    fn default() -> Self {
        Self::new()
    }
}

impl World {
    pub fn new() -> Self {
        let empty_archetype = Archetype::new(vec![TypeMetadata::new::<Entity>()]);

        Self {
            entities: Default::default(),
            free_list: Default::default(),
            archetypes: vec![empty_archetype],
            insert_map: Default::default(),
            remove_map: Default::default(),
            resources: Default::default(),
        }
    }
}

impl World {
    #[must_use]
    pub fn alloc(&mut self) -> Entity {
        if let Some(id) = self.free_list.pop() {
            let meta = &mut self.entities[id as usize];

            meta.idx = unsafe { self.archetypes[0].alloc() };

            let ent = Entity { id, gen: meta.gen };

            unsafe {
                self.archetypes[0].write(meta.idx, ent);
            }

            ent
        } else {
            let id = self.entities.len().try_into().unwrap();
            let gen = 0;

            let ty = 0;
            let idx = unsafe { self.archetypes[0].alloc() };

            let ent = Entity { id, gen };

            unsafe {
                self.archetypes[0].write(idx, ent);
            }

            self.entities.push(EntityMetadata { gen, ty, idx });

            ent
        }
    }

    pub fn free(&mut self, mut ent: Entity) {
        let meta = &mut self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen);

        meta.gen = meta.gen.checked_add(1).unwrap();
        ent.gen = meta.gen;

        let old_ty = meta.ty;
        meta.ty = 0;

        let old_archetype = &mut self.archetypes[old_ty as usize];

        unsafe {
            if old_archetype.free(meta.idx, true) {
                let moved_id = old_archetype.read::<Entity>(meta.idx).id;

                self.entities[moved_id as usize].idx = meta.idx;
            }
        }

        self.free_list.push(ent.id);
    }
}

impl World {
    pub(crate) fn archetypes(&self) -> &[Archetype] {
        &self.archetypes[1..]
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

            let pos = self
                .archetypes
                .iter_mut()
                .position(|archetype| archetype.match_(&types));

            if let Some(pos) = pos {
                new_ty = pos as u32;
            } else {
                new_ty = self.archetypes.len().try_into().unwrap();
                self.archetypes.push(Archetype::new(types));
            }

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

            let pos = self
                .archetypes
                .iter_mut()
                .position(|archetype| archetype.match_(&types));

            if let Some(pos) = pos {
                new_ty = pos as u32;
            } else {
                new_ty = self.archetypes.len() as u32;
                self.archetypes.push(Archetype::new(types));
            }

            self.remove_map.insert((meta.ty, TypeId::of::<B>()), new_ty);
            self.insert_map.insert((new_ty, TypeId::of::<B>()), meta.ty);
        }

        unsafe {
            let comps = B::read(&mut self.archetypes[meta.ty as usize], meta.idx);

            self.move_(ent.id, meta.ty, new_ty, meta.idx);

            Some(comps)
        }
    }

    unsafe fn move_(&mut self, id: u32, old_ty: u32, new_ty: u32, old_idx: u32) -> u32 {
        let old_archetype = &mut *self.archetypes.as_mut_ptr().add(old_ty as usize);
        let new_archetype = &mut *self.archetypes.as_mut_ptr().add(new_ty as usize);

        let new_idx = new_archetype.alloc();

        Archetype::move_(old_archetype, new_archetype, old_idx, new_idx);

        if old_archetype.free(old_idx, false) {
            let moved_id = old_archetype.read::<Entity>(old_idx).id;

            self.entities[moved_id as usize].idx = old_idx;
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
        let meta = &self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen);

        unsafe { self.archetypes[meta.ty as usize].get_mut::<C>(meta.idx) }
    }
}

impl World {
    pub fn insert_resource<R>(&mut self, res: R)
    where
        R: 'static,
    {
        self.resources.insert(res);
    }

    pub fn get_resource<R>(&self) -> Res<'_, R>
    where
        R: 'static,
    {
        self.resources.get::<R>()
    }

    pub fn get_resource_mut<R>(&self) -> ResMut<'_, R>
    where
        R: 'static,
    {
        self.resources.get_mut::<R>()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Entity {
    id: u32,
    gen: u32,
}

#[derive(Clone, Copy)]
struct EntityMetadata {
    gen: u32,
    ty: u32,
    idx: u32,
}

pub unsafe trait Bundle: 'static {
    fn insert(types: &mut Vec<TypeMetadata>);
    fn remove(types: &mut Vec<TypeMetadata>) -> Option<()>;
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
            fn insert(types: &mut Vec<TypeMetadata>) {
                $(TypeMetadata::insert::<$types>(types);)+
            }

            fn remove(types: &mut Vec<TypeMetadata>) -> Option<()> {
                $(TypeMetadata::remove::<$types>(types)?;)+

                Some(())
            }

            #[allow(non_snake_case)]
            unsafe fn write(self, archetype: &mut Archetype, idx: u32) {
                let ($($types,)+) = self;
                $(archetype.write(idx, $types);)+
            }

            #[allow(non_snake_case)]
            unsafe fn read(archetype: &mut Archetype, idx: u32) -> Self {
                $(let $types = archetype.read::<$types>(idx);)+
                ($($types,)+)
            }
        }
    };
}

impl_bundle_for_tuples!(A, B, C, D, E, F, G, H, I, J);

#[test]
fn it_works() {
    let mut world = World::new();

    let _1st = world.alloc();
    world.insert(_1st, (23_i32, 42_u64));

    let _2nd = world.alloc();
    world.insert(_2nd, (1_u8,));

    let _3rd = world.alloc();
    world.insert(_3rd, (0_u8,));

    let _4th = world.alloc();
    world.insert(_4th, (42_i32, 23_u64));

    {
        let val = world.get::<i32>(_1st).unwrap();
        assert_eq!(*val, 23);

        let mut val = world.get_mut::<u64>(_1st).unwrap();
        *val = 23;
    }

    {
        let val = world.get::<u8>(_2nd).unwrap();
        assert_eq!(*val, 1);

        let val = world.get::<u64>(_1st).unwrap();
        assert_eq!(*val, 23);
    }

    world.remove::<(i32,)>(_1st);

    {
        let val = world.get::<i32>(_1st);
        assert!(val.is_none());

        let val = world.get::<u64>(_1st).unwrap();
        assert_eq!(*val, 23);
    }

    world.free(_2nd);

    {
        let val = world.get::<u8>(_3rd).unwrap();
        assert_eq!(*val, 0);
    }

    let _5th = world.alloc();
    assert_eq!(_2nd.id, _5th.id);
    assert_ne!(_2nd.gen, _5th.gen);
}
