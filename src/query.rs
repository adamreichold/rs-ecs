use std::any::TypeId;
use std::cell::{Ref, RefMut};
use std::marker::PhantomData;
use std::mem::transmute;
use std::ptr::{null, null_mut};
use std::slice::Iter;

use crate::{
    archetype::Archetype,
    world::{Entity, World},
};

pub struct Query<S>
where
    S: QuerySpec,
{
    tag_gen: (u32, u32),
    types: Vec<(usize, <S::Fetch as Fetch<'static>>::Ty)>,
    refs: Vec<<S::Fetch as Fetch<'static>>::Ref>,
}

impl<S> Default for Query<S>
where
    S: QuerySpec,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<S> Query<S>
where
    S: QuerySpec,
{
    pub fn new() -> Self {
        Self {
            tag_gen: Default::default(),
            types: Default::default(),
            refs: Default::default(),
        }
    }

    pub fn iter<'q, F, T>(&'q mut self, world: &'q World, f: F) -> T
    where
        F: for<'i> FnOnce(QueryIter<'i, S>) -> T,
    {
        let tag_gen = world.tag_gen();
        let archetypes = world.archetypes();

        if self.tag_gen != tag_gen {
            self.tag_gen = tag_gen;

            self.find(archetypes);
        }

        let types: &'q Vec<(usize, <S::Fetch as Fetch<'q>>::Ty)> =
            unsafe { transmute(&self.types) };

        struct ClearOnDrop<'a, T>(&'a mut Vec<T>);

        impl<T> Drop for ClearOnDrop<'_, T> {
            fn drop(&mut self) {
                self.0.clear();
            }
        }

        let refs =
            ClearOnDrop::<'q, <S::Fetch as Fetch<'q>>::Ref>(unsafe { transmute(&mut self.refs) });

        for (idx, ty) in types {
            let archetype = &archetypes[*idx];

            if archetype.len() != 0 {
                refs.0.push(unsafe { S::Fetch::borrow(archetype, *ty) });
            }
        }

        let iter = QueryIter {
            types: types.iter(),
            archetypes,
            idx: 0,
            len: 0,
            ptr: S::Fetch::dangling(),
        };

        f(iter)
    }

    pub fn iter_mut<'q>(&'q mut self, world: &'q mut World) -> QueryIter<'q, S> {
        let tag_gen = world.tag_gen();
        let archetypes = world.archetypes();

        if self.tag_gen != tag_gen {
            self.tag_gen = tag_gen;

            self.find(archetypes);
        }

        let types: &'q Vec<(usize, <S::Fetch as Fetch<'q>>::Ty)> =
            unsafe { transmute(&self.types) };

        QueryIter {
            types: types.iter(),
            archetypes,
            idx: 0,
            len: 0,
            ptr: S::Fetch::dangling(),
        }
    }

    #[cold]
    fn find(&mut self, archetypes: &[Archetype]) {
        self.types.clear();

        for (idx, archetype) in archetypes.iter().enumerate() {
            if let Some(ty) = S::Fetch::find(archetype) {
                self.types.push((idx, ty));
            }
        }
    }

    pub fn with<C>(self) -> Query<With<S, C>>
    where
        C: 'static,
    {
        Query::new()
    }

    pub fn without<C>(self) -> Query<Without<S, C>>
    where
        C: 'static,
    {
        Query::new()
    }
}

pub struct QueryIter<'q, S>
where
    S: QuerySpec,
{
    types: Iter<'q, (usize, <S::Fetch as Fetch<'q>>::Ty)>,
    archetypes: &'q [Archetype],
    idx: u32,
    len: u32,
    ptr: <S::Fetch as Fetch<'q>>::Ptr,
}

impl<'q, S> Iterator for QueryIter<'q, S>
where
    S: QuerySpec,
{
    type Item = <S::Fetch as Fetch<'q>>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.idx != self.len {
                let val = unsafe { S::Fetch::deref(self.ptr, self.idx) };
                self.idx += 1;
                return Some(val);
            } else {
                let (idx, ty) = self.types.next()?;
                let archetype = &self.archetypes[*idx];
                self.idx = 0;
                self.len = archetype.len();
                self.ptr = unsafe { S::Fetch::pointer(archetype, *ty) };
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<S> ExactSizeIterator for QueryIter<'_, S>
where
    S: QuerySpec,
{
    fn len(&self) -> usize {
        let len = self
            .types
            .clone()
            .map(|(idx, _)| self.archetypes[*idx].len())
            .sum::<u32>()
            + self.len
            - self.idx;
        len as usize
    }
}

pub trait QuerySpec {
    #[doc(hidden)]
    type Fetch: for<'a> Fetch<'a>;
}

pub unsafe trait Fetch<'q> {
    type Ty: Copy;
    type Ref;
    type Ptr: Copy;

    type Item;

    fn find(archetype: &Archetype) -> Option<Self::Ty>;
    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref;
    unsafe fn pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr;

    fn dangling() -> Self::Ptr;
    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item;
}

impl<'a, C> QuerySpec for &'a C
where
    C: 'static,
{
    type Fetch = FetchRead<C>;
}

pub struct FetchRead<C>(PhantomData<C>);

unsafe impl<'q, C> Fetch<'q> for FetchRead<C>
where
    C: 'static,
{
    type Ty = usize;
    type Ref = Ref<'q, ()>;
    type Ptr = *const C;

    type Item = &'q C;

    fn find(archetype: &Archetype) -> Option<Self::Ty> {
        archetype.find::<C>()
    }

    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref {
        archetype.borrow::<C>(ty)
    }

    unsafe fn pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        archetype.pointer::<C>(ty)
    }

    fn dangling() -> Self::Ptr {
        null()
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        &*ptr.add(idx as usize)
    }
}

impl<'a, C> QuerySpec for &'a mut C
where
    C: 'static,
{
    type Fetch = FetchWrite<C>;
}

pub struct FetchWrite<C>(PhantomData<C>);

unsafe impl<'q, C> Fetch<'q> for FetchWrite<C>
where
    C: 'static,
{
    type Ty = usize;
    type Ref = RefMut<'q, ()>;
    type Ptr = *mut C;

    type Item = &'q mut C;

    fn find(archetype: &Archetype) -> Option<Self::Ty> {
        if TypeId::of::<C>() == TypeId::of::<Entity>() {
            panic!("Entity cannot be queried mutably");
        }

        archetype.find::<C>()
    }

    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref {
        archetype.borrow_mut::<C>(ty)
    }

    unsafe fn pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        archetype.pointer::<C>(ty)
    }

    fn dangling() -> Self::Ptr {
        null_mut()
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        &mut *ptr.add(idx as usize)
    }
}

impl<S> QuerySpec for Option<S>
where
    S: QuerySpec,
{
    type Fetch = TryFetch<S::Fetch>;
}

pub struct TryFetch<F>(PhantomData<F>);

unsafe impl<'q, F> Fetch<'q> for TryFetch<F>
where
    F: Fetch<'q>,
{
    type Ty = Option<F::Ty>;
    type Ref = Option<F::Ref>;
    type Ptr = Option<F::Ptr>;

    type Item = Option<F::Item>;

    fn find(archetype: &Archetype) -> Option<Self::Ty> {
        Some(F::find(archetype))
    }

    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref {
        ty.map(|ty| F::borrow(archetype, ty))
    }

    unsafe fn pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        ty.map(|ty| F::pointer(archetype, ty))
    }

    fn dangling() -> Self::Ptr {
        None
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        ptr.map(|ptr| F::deref(ptr, idx))
    }
}

pub struct With<S, C>(PhantomData<(S, C)>);

impl<S, C> QuerySpec for With<S, C>
where
    S: QuerySpec,
    C: 'static,
{
    type Fetch = FetchWith<S::Fetch, C>;
}

pub struct FetchWith<F, C>(PhantomData<(F, C)>);

unsafe impl<'q, F, C> Fetch<'q> for FetchWith<F, C>
where
    F: Fetch<'q>,
    C: 'static,
{
    type Ty = F::Ty;
    type Ref = F::Ref;
    type Ptr = F::Ptr;

    type Item = F::Item;

    fn find(archetype: &Archetype) -> Option<Self::Ty> {
        match archetype.find::<C>() {
            Some(_) => F::find(archetype),
            None => None,
        }
    }

    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref {
        F::borrow(archetype, ty)
    }

    unsafe fn pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        F::pointer(archetype, ty)
    }

    fn dangling() -> Self::Ptr {
        F::dangling()
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        F::deref(ptr, idx)
    }
}

pub struct Without<S, C>(PhantomData<(S, C)>);

impl<S, C> QuerySpec for Without<S, C>
where
    S: QuerySpec,
    C: 'static,
{
    type Fetch = FetchWithout<S::Fetch, C>;
}

pub struct FetchWithout<F, C>(PhantomData<(F, C)>);

unsafe impl<'q, F, C> Fetch<'q> for FetchWithout<F, C>
where
    F: Fetch<'q>,
    C: 'static,
{
    type Ty = F::Ty;
    type Ref = F::Ref;
    type Ptr = F::Ptr;

    type Item = F::Item;

    fn find(archetype: &Archetype) -> Option<Self::Ty> {
        match archetype.find::<C>() {
            None => F::find(archetype),
            Some(_) => None,
        }
    }

    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref {
        F::borrow(archetype, ty)
    }

    unsafe fn pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        F::pointer(archetype, ty)
    }

    fn dangling() -> Self::Ptr {
        F::dangling()
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        F::deref(ptr, idx)
    }
}

macro_rules! impl_fetch_for_tuples {
    () => {};

    ($head:ident $(,$tail:ident)*) => {
        impl_fetch_for_tuples!($($tail),*);
        impl_fetch_for_tuples!(@impl $head $(,$tail)*);
    };

    (@impl $($types:ident),+) => {
        impl<$($types),+> QuerySpec for ($($types,)+)
        where
            $($types: QuerySpec,)+
        {
            type Fetch = ($($types::Fetch,)+);
        }

        unsafe impl<'q, $($types),+> Fetch<'q> for ($($types,)+)
        where
            $($types: Fetch<'q>,)+
        {
            type Ty = ($($types::Ty,)+);
            type Ref = ($($types::Ref,)+);
            type Ptr = ($($types::Ptr,)+);

            type Item = ($($types::Item,)+);

            #[allow(non_snake_case)]
            fn find(archetype: &Archetype) -> Option<Self::Ty> {
                $(let $types = $types::find(archetype)?;)+

                Some(($($types,)+))
            }

            #[allow(non_snake_case)]
            unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref {
                let ($($types,)+) = ty;

                ($($types::borrow(archetype, $types),)+)
            }

            #[allow(non_snake_case)]
            unsafe fn pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
                let ($($types,)+) = ty;

                ($($types::pointer(archetype, $types),)+)
            }

            fn dangling() -> Self::Ptr {
                ($($types::dangling(),)+)
            }

            #[allow(non_snake_case)]
            unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
                let ($($types,)+) = ptr;

                ($($types::deref($types, idx),)+)
            }
        }
    };
}

impl_fetch_for_tuples!(A, B, C, D, E, F, G, H, I, J);

#[cfg(test)]
mod tests {
    use super::*;

    fn spawn_three(world: &mut World) {
        let ent = world.alloc();
        world.insert(ent, (23_i32, 42_u64));

        let ent = world.alloc();
        world.insert(ent, (1_i32, 2_i8, 3_u16));

        let ent = world.alloc();
        world.insert(ent, (42_i32, 23_u64, true));
    }

    #[test]
    fn queries_can_be_used_once() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new();

        let comps = query.iter(&world, |iter| iter.copied().collect::<Vec<_>>());
        assert_eq!(&comps, &[23, 1, 42]);
    }

    #[test]
    fn queries_can_be_reused() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new();

        let comps1 = query.iter(&world, |iter| iter.copied().collect::<Vec<_>>());
        assert_eq!(&comps1, &[23, 1, 42]);

        let comps2 = query.iter(&world, |iter| iter.copied().collect::<Vec<_>>());
        assert_eq!(&comps2, &comps1);
    }

    #[test]
    fn queries_can_be_reused_after_adding_an_archetype() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new();

        let comps1 = query.iter(&world, |iter| iter.copied().collect::<Vec<_>>());
        assert_eq!(&comps1, &[23, 1, 42]);

        let ent = world.alloc();
        world.insert(ent, (0_i64,));

        let comps2 = query.iter(&world, |iter| iter.copied().collect::<Vec<_>>());
        assert_eq!(&comps2, &comps1);
    }

    #[test]
    fn queries_can_be_used_without_borrowing() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new();

        let comps = query.iter_mut(&mut world).copied().collect::<Vec<_>>();
        assert_eq!(&comps, &[23, 1, 42]);
    }

    #[test]
    fn queries_can_modify_components() {
        let mut world = World::new();

        spawn_three(&mut world);

        {
            let mut query = Query::<&mut i32>::new();

            query.iter(&world, |iter| {
                for comp in iter {
                    *comp *= -1;
                }
            });
        }

        let mut query = Query::<&i32>::new();
        let comps = query.iter(&world, |iter| iter.copied().collect::<Vec<_>>());

        assert_eq!(&comps, &[-23, -1, -42]);
    }

    #[test]
    fn entities_can_be_queried_immutably() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&Entity>::new();
        let cnt = query.iter(&world, |iter| iter.count());

        assert_eq!(cnt, 3);
    }

    #[test]
    #[should_panic]
    fn entities_cannot_be_queried_mutably() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&mut Entity>::new();
        let _ = query.iter(&world, |_iter| {});
    }

    #[test]
    fn try_exposes_optional_components() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<Option<&u64>>::new();
        let cnt = query.iter(&world, |iter| iter.count());
        let cnt_some = query.iter(&world, |iter| iter.flatten().count());

        assert_eq!(cnt, 3);
        assert_eq!(cnt_some, 2);
    }

    #[test]
    fn with_checks_for_presence() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new().with::<bool>();
        let sum = query.iter(&world, |iter| iter.sum::<i32>());

        assert_eq!(sum, 42);
    }

    #[test]
    fn without_checks_for_absence() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new().without::<bool>();
        let sum = query.iter(&world, |iter| iter.sum::<i32>());

        assert_eq!(sum, 23 + 1);
    }
}
