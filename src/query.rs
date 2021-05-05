use std::cell::{Ref, RefMut};
use std::marker::PhantomData;
use std::mem::transmute;
use std::ptr::{null, null_mut};

use crate::{archetype::Archetype, world::World};

pub struct Query<S>
where
    S: QuerySpec,
{
    refs: Refs<'static, S>,
    vals: Vals<'static, S>,
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
            refs: Default::default(),
            vals: Default::default(),
        }
    }

    pub fn iter<'q>(&'q mut self, world: &'q World) -> QueryIter<'q, S> {
        debug_assert!(self.refs.is_empty());
        debug_assert!(self.vals.is_empty());

        let refs: &'q mut Refs<'q, S> = unsafe { transmute(&mut self.refs) };
        let vals: &'q mut Vals<'q, S> = unsafe { transmute(&mut self.vals) };

        for archetype in world.archetypes() {
            let len = archetype.len();
            if len == 0 {
                continue;
            }

            if let Some(ty) = S::Fetch::find(archetype) {
                let (ref_, ptr) = S::Fetch::borrow(archetype, ty);

                refs.push(ref_);
                vals.push((len, ptr));
            }
        }

        QueryIter {
            refs,
            vals,
            idx: 0,
            len: 0,
            ptr: S::Fetch::dangling(),
        }
    }

    pub fn with<C>(self) -> Query<With<S, C>>
    where
        C: 'static,
    {
        Query {
            refs: self.refs,
            vals: self.vals,
        }
    }

    pub fn without<C>(self) -> Query<Without<S, C>>
    where
        C: 'static,
    {
        Query {
            refs: self.refs,
            vals: self.vals,
        }
    }
}

pub trait QuerySpec {
    type Fetch: for<'a> Fetch<'a>;
}

pub unsafe trait Fetch<'q> {
    type Ty: Copy;
    type Ref;
    type Ptr: Copy;

    type Item;

    fn find(archetype: &Archetype) -> Option<Self::Ty>;
    fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> (Self::Ref, Self::Ptr);

    fn dangling() -> Self::Ptr;
    unsafe fn get(ptr: Self::Ptr, idx: u32) -> Self::Item;
}

type Refs<'q, S> = Vec<<<S as QuerySpec>::Fetch as Fetch<'q>>::Ref>;

type Vals<'q, S> = Vec<(u32, <<S as QuerySpec>::Fetch as Fetch<'q>>::Ptr)>;

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

    fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> (Self::Ref, Self::Ptr) {
        archetype.borrow::<C>(ty)
    }

    fn dangling() -> Self::Ptr {
        null()
    }

    unsafe fn get(ptr: Self::Ptr, idx: u32) -> Self::Item {
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
        archetype.find::<C>()
    }

    fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> (Self::Ref, Self::Ptr) {
        archetype.borrow_mut::<C>(ty)
    }

    fn dangling() -> Self::Ptr {
        null_mut()
    }

    unsafe fn get(ptr: Self::Ptr, idx: u32) -> Self::Item {
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

    fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> (Self::Ref, Self::Ptr) {
        ty.map_or((None, None), |ty| {
            let (ref_, ptr) = F::borrow(archetype, ty);
            (Some(ref_), Some(ptr))
        })
    }

    fn dangling() -> Self::Ptr {
        None
    }

    unsafe fn get(ptr: Self::Ptr, idx: u32) -> Self::Item {
        ptr.map(|ptr| F::get(ptr, idx))
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

    fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> (Self::Ref, Self::Ptr) {
        F::borrow(archetype, ty)
    }

    fn dangling() -> Self::Ptr {
        F::dangling()
    }

    unsafe fn get(ptr: Self::Ptr, idx: u32) -> Self::Item {
        F::get(ptr, idx)
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

    fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> (Self::Ref, Self::Ptr) {
        F::borrow(archetype, ty)
    }

    fn dangling() -> Self::Ptr {
        F::dangling()
    }

    unsafe fn get(ptr: Self::Ptr, idx: u32) -> Self::Item {
        F::get(ptr, idx)
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
            fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> (Self::Ref, Self::Ptr) {
                let ($($types,)+) = ty;

                $(let $types = $types::borrow(archetype, $types);)+

                (($($types.0,)+), ($($types.1,)+))
            }

            fn dangling() -> Self::Ptr {
                ($($types::dangling(),)+)
            }

            #[allow(non_snake_case)]
            unsafe fn get(ptr: Self::Ptr, idx: u32) -> Self::Item {
                let ($($types,)+) = ptr;

                ($($types::get($types, idx),)+)
            }
        }
    };
}

impl_fetch_for_tuples!(A, B, C, D, E, F, G, H, I, J);

pub struct QueryIter<'q, S>
where
    S: QuerySpec,
{
    refs: &'q mut Refs<'q, S>,
    vals: &'q mut Vals<'q, S>,
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
                let val = unsafe { S::Fetch::get(self.ptr, self.idx) };
                self.idx += 1;
                return Some(val);
            } else {
                let (len, ptr) = self.vals.pop()?;
                self.idx = 0;
                self.len = len;
                self.ptr = ptr;
                continue;
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
        let len = self.vals.iter().map(|(len, _)| *len).sum::<u32>() + self.len - self.idx;
        len as usize
    }
}

impl<S> Drop for QueryIter<'_, S>
where
    S: QuerySpec,
{
    fn drop(&mut self) {
        self.refs.clear();
        self.vals.clear();
    }
}

#[test]
fn it_works() {
    use crate::world::Entity;

    let mut world = World::new();

    let _1st = world.alloc();
    world.insert(_1st, (23_i32, 42_u64));

    let _2nd = world.alloc();
    world.insert(_2nd, (1_i32,));

    let _3rd = world.alloc();
    world.insert(_3rd, (42_i32, 23_u64, true));

    let mut query = Query::<(&Entity, &mut i32)>::new();
    let mut entities = Vec::new();

    for (ent, val) in query.iter(&world) {
        *val *= -1;

        entities.push(*ent);
    }

    {
        let val = world.get::<i32>(_1st).unwrap();
        assert_eq!(*val, -23);

        let val = world.get::<i32>(_2nd).unwrap();
        assert_eq!(*val, -1);

        let val = world.get::<i32>(_3rd).unwrap();
        assert_eq!(*val, -42);

        entities.sort_unstable();
        assert_eq!(entities, vec![_1st, _2nd, _3rd]);
    }

    let mut query = Query::<(Option<&bool>,)>::new();
    let mut some = 0;
    let mut none = 0;

    for (val,) in query.iter(&world) {
        if let Some(val) = val {
            assert!(val);

            some += 1;
        } else {
            none += 1;
        }
    }

    assert_eq!(some, 1);
    assert_eq!(none, 2);

    let mut query = Query::<&i32>::new().without::<bool>();
    let sum = query.iter(&world).sum::<i32>();

    assert_eq!(sum, -23 - 1);
}
