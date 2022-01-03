use std::any::TypeId;
use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::mem::{transmute, ManuallyDrop};
use std::ptr::NonNull;
use std::slice::Iter;

use crate::{
    archetype::{Archetype, Ref, RefMut},
    world::{Entity, EntityMetadata, World},
};

#[cfg(feature = "rayon")]
use crate::rayon::QueryParIter;

/// Query to get an iterator over all entities with a certain combination of components.
///
/// Queries are specified through their type argument, by composing the type of their result.
/// The following type specifications are possible:
///
/// * `&C` - shared, immutable reference to components of type `C`
/// * `&mut C` - exclusive, mutable reference
/// * `(P, Q, R)` - combine multiple queries
/// * `Option<Q>` - optional component(s)
/// * `With<Q, C>` to filter `Q` for presence of `C`
/// * `Without<Q, C>` to filter `Q` for absence of `C`
/// * `Matches<Q> to indicate which entities match `Q`
///
/// Note that [Entities](Entity) are components themselves, so they can be optionally obtained in a query,
/// like `Query<Entity, &C, &mut D>`.
///
/// Queries are provided as stand-alone structs to allow for prepared queries that can be
/// re-used, as an optimzation. Hence, queries need to borrow the [World] before their results
/// can be iterated (see [Query::borrow]).
///
/// # Examples
///
/// ```
/// # use rs_ecs::*;
/// let mut world = World::new();
///
/// let entity1 = world.alloc();
/// world.insert(entity1, (42_i32, 23_u32, 1.0_f32));
///
/// let entity2 = world.alloc();
/// world.insert(entity2, (0_i32, true));
///
/// let mut query = Query::<(&mut i32, Option<(&u32, &mut f32)>)>::new();
/// for (i, opt) in query.borrow(&world).iter() {
///     if let Some((u, f)) = opt {
///         *i += *u as i32;
///         *f += 1.0
///     } else {
///         *i -= 1;
///     }
/// }
///
/// assert_eq!(*world.get::<i32>(entity1).unwrap(), 65);
/// assert_eq!(*world.get::<f32>(entity1).unwrap(), 2.0);
/// assert_eq!(*world.get::<i32>(entity2).unwrap(), -1);
/// ```
///
/// Use of a prepared query that is stored and reused for optimization:
///
/// ```
/// # use rs_ecs::*;
/// #[derive(Default)]
/// struct System {
///     query: Query<(&'static i32, &'static mut bool)>
/// }
///
/// impl System {
///     pub fn update(&mut self, world: &World) {
///         for (i, b) in self.query.borrow(world).iter() {
///             *b = *i >= 0;
///         }
///     }
/// }
///
/// fn main() {
///     let mut world = World::new();
///
///     let entity = world.alloc();
///     world.insert(entity, (23_i32, false));
///
///     let mut system = System::default();
///
///     for _ in 0..42 {
///         system.update(&world);
///     }
/// }
/// ```
///
pub struct Query<S>
where
    S: QuerySpec,
{
    tag_gen: (u32, u16),
    types: Box<[(u16, <S::Fetch as Fetch<'static>>::Ty)]>,
    refs: Vec<ManuallyDrop<<S::Fetch as Fetch<'static>>::Ref>>,
    ptrs: Box<[Option<<S::Fetch as Fetch<'static>>::Ptr>]>,
}

#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<S> Send for Query<S> where S: QuerySpec {}

impl<S> Default for Query<S>
where
    S: QuerySpec,
{
    /// Create a query.
    fn default() -> Self {
        Self::new()
    }
}

impl<S> Query<S>
where
    S: QuerySpec,
{
    /// Create a query.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut immutable_query = Query::<(&i32,)>::new();
    /// let mut mutable_query = Query::<(&i32, &mut bool)>::new();
    /// let mut query_with_entity = Query::<(&Entity, &i32, &mut bool)>::new();
    /// ```
    pub fn new() -> Self {
        Self {
            tag_gen: Default::default(),
            types: Default::default(),
            refs: Default::default(),
            ptrs: Default::default(),
        }
    }

    /// Borrow the [World] to allow for iterating the query.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    /// let mut query = Query::<(&i32, &bool)>::new();
    /// let mut borrow = query.borrow(&world);
    ///
    /// for (i, b) in borrow.iter() {
    ///     println!("{}, {}", i, b);
    /// }
    /// ```
    pub fn borrow<'w>(&'w mut self, world: &'w World) -> QueryRef<'w, S> {
        if self.tag_gen != world.tag_gen() {
            self.find(world);
        }

        self.refs.clear();

        let ref_ = QueryRef {
            world,
            types: unsafe { transmute(&*self.types) },
            refs: unsafe { transmute(&mut self.refs) },
            ptrs: unsafe { transmute(&mut *self.ptrs) },
        };

        for (idx, ty) in ref_.types {
            let archetype = &world.archetypes[*idx as usize];

            if archetype.len() != 0 {
                ref_.refs.push(unsafe { S::Fetch::borrow(archetype, *ty) });
            }
        }

        ref_
    }

    #[cold]
    #[inline(never)]
    fn find(&mut self, world: &World) {
        self.types = world
            .archetypes
            .iter()
            .enumerate()
            .filter_map(|(idx, archetype)| S::Fetch::find(archetype).map(|ty| (idx as u16, ty)))
            .collect();

        self.ptrs = world.archetypes.iter().map(|_| None).collect();

        self.tag_gen = world.tag_gen();
    }
}

/// Borrow of the [World] for a [Query]. Required to obtain an iterator.
pub struct QueryRef<'w, S>
where
    S: QuerySpec,
{
    world: &'w World,
    types: &'w [(u16, <S::Fetch as Fetch<'w>>::Ty)],
    refs: &'w mut Vec<<S::Fetch as Fetch<'w>>::Ref>,
    ptrs: &'w mut [Option<<S::Fetch as Fetch<'w>>::Ptr>],
}

impl<S> QueryRef<'_, S>
where
    S: QuerySpec,
{
    /// Visit all entities matching the query.
    pub fn for_each<'q, F>(&'q mut self, mut f: F)
    where
        F: FnMut(<S::Fetch as Fetch<'q>>::Item),
    {
        let types: &'q [(u16, <S::Fetch as Fetch<'q>>::Ty)] = unsafe { transmute(self.types) };

        for (idx, ty) in types {
            let archetype = &self.world.archetypes[*idx as usize];

            let ptr = unsafe { S::Fetch::base_pointer(archetype, *ty) };

            for idx in 0..archetype.len() {
                let val = unsafe { S::Fetch::deref(ptr, idx) };

                f(val);
            }
        }
    }

    /// Create an iterator over the entities matching the query.
    pub fn iter<'q>(&'q mut self) -> QueryIter<'q, S> {
        let types: &'q [(u16, <S::Fetch as Fetch<'q>>::Ty)] = unsafe { transmute(self.types) };

        QueryIter {
            types: types.iter(),
            archetypes: &self.world.archetypes,
            idx: 0,
            len: 0,
            ptr: S::Fetch::dangling(),
        }
    }

    #[cfg(feature = "rayon")]
    /// Create a parallel iterator over the entities matching the query.
    pub fn par_iter<'q>(&'q mut self) -> QueryParIter<'q, S>
    where
        <S::Fetch as Fetch<'q>>::Ty: Send + Sync,
        <S::Fetch as Fetch<'q>>::Item: Send,
    {
        let types: &'q [(u16, <S::Fetch as Fetch<'q>>::Ty)] = unsafe { transmute(self.types) };

        QueryParIter::new(types, &self.world.archetypes)
    }

    /// Create a map of the entities matching the query.
    ///
    /// This is an alternative to [get](World::get) and [get_mut](World::get_mut) for repeated calls, to amortize the set-up costs.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity = world.alloc();
    /// world.insert(entity, (42_i32, 1.0_f32));
    ///
    /// let mut query = Query::<(&i32, &f32)>::new();
    /// let mut query = query.borrow(&world);
    /// let mut query = query.map();
    ///
    /// let (i, f) = query.get_mut(entity).unwrap();
    ///
    /// assert_eq!(*i, 42);
    /// assert_eq!(*f, 1.0);
    /// ```
    pub fn map<'q>(&'q mut self) -> QueryMap<'q, S> {
        let types: &'q [(u16, <S::Fetch as Fetch<'q>>::Ty)] = unsafe { transmute(self.types) };

        let ptrs: &'q mut [Option<<S::Fetch as Fetch<'q>>::Ptr>] =
            unsafe { transmute(&mut *self.ptrs) };

        ptrs.fill(None);

        for (idx, ty) in types {
            let archetype = &self.world.archetypes[*idx as usize];

            let ptr = unsafe { S::Fetch::base_pointer(archetype, *ty) };

            ptrs[*idx as usize] = Some(ptr);
        }

        QueryMap {
            entities: &self.world.entities,
            ptrs,
        }
    }
}

impl<S> Drop for QueryRef<'_, S>
where
    S: QuerySpec,
{
    fn drop(&mut self) {
        self.refs.clear();
    }
}

/// Used to iterate through the entities which match a certain [Query].
pub struct QueryIter<'q, S>
where
    S: QuerySpec,
{
    types: Iter<'q, (u16, <S::Fetch as Fetch<'q>>::Ty)>,
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
                let archetype = &self.archetypes[*idx as usize];
                self.idx = 0;
                self.len = archetype.len();
                self.ptr = unsafe { S::Fetch::base_pointer(archetype, *ty) };
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
            .map(|(idx, _)| self.archetypes[*idx as usize].len())
            .sum::<u32>()
            + self.len
            - self.idx;
        len as usize
    }
}

impl<S> FusedIterator for QueryIter<'_, S> where S: QuerySpec {}

/// Provides random access to the entities which match a certain [Query].
pub struct QueryMap<'q, S>
where
    S: QuerySpec,
{
    entities: &'q [EntityMetadata],
    ptrs: &'q [Option<<S::Fetch as Fetch<'q>>::Ptr>],
}

impl<S> QueryMap<'_, S>
where
    S: QuerySpec,
{
    /// Access the queried components of the given [Entity]
    ///
    /// # Examples
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let mut world = World::new();
    ///
    /// let entity1 = world.alloc();
    /// world.insert(entity1, (42_i32, 1.0_f32));
    ///
    /// let entity2 = world.alloc();
    /// world.insert(entity2, (23_i32,));
    ///
    /// let mut query = Query::<(&i32, Option<&f32>)>::new();
    /// let mut query = query.borrow(&world);
    /// let mut query = query.map();
    ///
    /// let (i1, f1) = query.get(entity1).unwrap();
    /// let (i2, f2) = query.get(entity2).unwrap();
    ///
    /// assert_eq!(*i1, 42);
    /// assert_eq!(f1.copied(), Some(1.0));
    /// assert_eq!(*i2, 23);
    /// assert_eq!(f2.copied(), None);
    /// ```
    pub fn get<'m>(&'m self, ent: Entity) -> Option<<S::Fetch as Fetch<'m>>::Item>
    where
        S::Fetch: FetchShared,
    {
        let meta = self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        let ptr: &'m Option<<S::Fetch as Fetch<'m>>::Ptr> =
            unsafe { transmute(self.ptrs.get_unchecked(meta.ty as usize)) };

        ptr.map(|ptr| unsafe { S::Fetch::deref(ptr, meta.idx) })
    }

    /// Exclusively access the queried components of the given [Entity]
    pub fn get_mut<'m>(&'m mut self, ent: Entity) -> Option<<S::Fetch as Fetch<'m>>::Item> {
        let meta = self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        let ptr: &'m Option<<S::Fetch as Fetch<'m>>::Ptr> =
            unsafe { transmute(self.ptrs.get_unchecked(meta.ty as usize)) };

        ptr.map(|ptr| unsafe { S::Fetch::deref(ptr, meta.idx) })
    }
}

/// Type level specification of a query for a certain set of components.
pub trait QuerySpec {
    #[doc(hidden)]
    type Fetch: for<'a> Fetch<'a>;
}

#[allow(clippy::missing_safety_doc)]
pub unsafe trait Fetch<'q> {
    type Ty: Copy;
    type Ref;
    type Ptr: Copy;

    type Item;

    fn find(archetype: &Archetype) -> Option<Self::Ty>;
    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref;
    unsafe fn base_pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr;

    fn dangling() -> Self::Ptr;
    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item;
}

#[allow(clippy::missing_safety_doc)]
pub unsafe trait FetchShared {}

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
    type Ty = u16;
    type Ref = Ref<'q>;
    type Ptr = NonNull<C>;

    type Item = &'q C;

    fn find(archetype: &Archetype) -> Option<Self::Ty> {
        archetype.find::<C>()
    }

    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref {
        archetype.borrow::<C>(ty)
    }

    unsafe fn base_pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        NonNull::new_unchecked(archetype.base_pointer::<C>(ty))
    }

    fn dangling() -> Self::Ptr {
        NonNull::dangling()
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        &*ptr.as_ptr().add(idx as usize)
    }
}

unsafe impl<C> FetchShared for FetchRead<C> {}

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
    type Ty = u16;
    type Ref = RefMut<'q>;
    type Ptr = NonNull<C>;

    type Item = &'q mut C;

    fn find(archetype: &Archetype) -> Option<Self::Ty> {
        assert_ne!(
            TypeId::of::<C>(),
            TypeId::of::<Entity>(),
            "Entity cannot be queried mutably"
        );

        archetype.find::<C>()
    }

    unsafe fn borrow(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ref {
        archetype.borrow_mut::<C>(ty)
    }

    unsafe fn base_pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        NonNull::new_unchecked(archetype.base_pointer::<C>(ty))
    }

    fn dangling() -> Self::Ptr {
        NonNull::dangling()
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        &mut *ptr.as_ptr().add(idx as usize)
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

    unsafe fn base_pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        ty.map(|ty| F::base_pointer(archetype, ty))
    }

    fn dangling() -> Self::Ptr {
        None
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        ptr.map(|ptr| F::deref(ptr, idx))
    }
}

unsafe impl<F> FetchShared for TryFetch<F> where F: FetchShared {}

/// A query specification to iterate over entities with a certain component,
/// but without borrowing that component.
///
/// # Examples
///
/// A query for components of type `u32` and `bool`,
/// only matching entities with a component of type `f32`.
///
/// ```
/// # use rs_ecs::*;
/// let query = Query::<With<(&u32, &bool), f32>>::new();
/// ```
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

    unsafe fn base_pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        F::base_pointer(archetype, ty)
    }

    fn dangling() -> Self::Ptr {
        F::dangling()
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        F::deref(ptr, idx)
    }
}

unsafe impl<F, C> FetchShared for FetchWith<F, C> where F: FetchShared {}

/// A query specification to iterate over entities without a certain component.
///
/// # Examples
///
/// A query for components of type `u32` and `bool`,
/// only matching entities without a component of type `f32`.
///
/// ```
/// # use rs_ecs::*;
/// let query = Query::<Without<(&u32, &bool), f32>>::new();
/// ```
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

    unsafe fn base_pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        F::base_pointer(archetype, ty)
    }

    fn dangling() -> Self::Ptr {
        F::dangling()
    }

    unsafe fn deref(ptr: Self::Ptr, idx: u32) -> Self::Item {
        F::deref(ptr, idx)
    }
}

unsafe impl<F, C> FetchShared for FetchWithout<F, C> where F: FetchShared {}

/// A query specification to indicate which entities match the inner query,
/// but without borrowing any components.
///
/// # Examples
///
/// ```
/// # use rs_ecs::*;
/// let mut world = World::new();
///
/// let entity1 = world.alloc();
/// world.insert(entity1, (42_i32, 1.0_f32));
///
/// let entity2 = world.alloc();
/// world.insert(entity2, (23_i32,));
///
/// let mut query = Query::<(&i32, Matches<&f32>)>::new();
/// let mut query = query.borrow(&world);
/// let mut query = query.map();
///
/// let (i1, f1) = query.get(entity1).unwrap();
/// assert_eq!(*i1, 42);
/// assert!(f1);
///
/// let (i2, f2) = query.get(entity2).unwrap();
/// assert_eq!(*i2, 23);
/// assert!(!f2);
/// ```
pub struct Matches<S>(PhantomData<S>);

impl<S> QuerySpec for Matches<S>
where
    S: QuerySpec,
{
    type Fetch = FetchMatches<S::Fetch>;
}

pub struct FetchMatches<F>(PhantomData<F>);

unsafe impl<'q, F> Fetch<'q> for FetchMatches<F>
where
    F: Fetch<'q>,
{
    type Ty = bool;
    type Ref = ();
    type Ptr = bool;

    type Item = bool;

    fn find(archetype: &Archetype) -> Option<Self::Ty> {
        Some(F::find(archetype).is_some())
    }

    unsafe fn borrow(_archetype: &'q Archetype, _ty: Self::Ty) -> Self::Ref {}

    unsafe fn base_pointer(_archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
        ty
    }

    fn dangling() -> Self::Ptr {
        false
    }

    unsafe fn deref(ptr: Self::Ptr, _idx: u32) -> Self::Item {
        ptr
    }
}

unsafe impl<F> FetchShared for FetchMatches<F> {}

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
            unsafe fn base_pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr {
                let ($($types,)+) = ty;

                ($($types::base_pointer(archetype, $types),)+)
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

        unsafe impl<$($types),+> FetchShared for ($($types,)+)
        where
            $($types: FetchShared,)+
        {
        }
    };
}

impl_fetch_for_tuples!(J, I, H, G, F, E, D, C, B, A);

#[cfg(test)]
mod tests {
    use super::*;

    use std::mem::{forget, size_of};
    use std::panic::{catch_unwind, AssertUnwindSafe};

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

        let comps = query.borrow(&world).iter().copied().collect::<Vec<_>>();
        assert_eq!(&comps, &[23, 1, 42]);
    }

    #[test]
    fn queries_can_be_reused() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new();

        let comps1 = query.borrow(&world).iter().copied().collect::<Vec<_>>();
        assert_eq!(&comps1, &[23, 1, 42]);

        let comps2 = query.borrow(&world).iter().copied().collect::<Vec<_>>();
        assert_eq!(&comps2, &comps1);
    }

    #[test]
    fn queries_can_be_reused_after_adding_an_archetype() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new();

        let comps1 = query.borrow(&world).iter().copied().collect::<Vec<_>>();
        assert_eq!(&comps1, &[23, 1, 42]);

        let ent = world.alloc();
        world.insert(ent, (0_i64,));

        let comps2 = query.borrow(&world).iter().copied().collect::<Vec<_>>();
        assert_eq!(&comps2, &comps1);
    }

    #[test]
    fn queries_can_modify_components() {
        let mut world = World::new();

        spawn_three(&mut world);

        {
            let mut query = Query::<&mut i32>::new();

            for comp in query.borrow(&world).iter() {
                *comp *= -1;
            }
        }

        let mut query = Query::<&i32>::new();
        let comps = query.borrow(&world).iter().copied().collect::<Vec<_>>();

        assert_eq!(&comps, &[-23, -1, -42]);
    }

    #[test]
    fn forgotten_query_ref_does_not_use_after_free() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&mut i32>::new();
        forget(query.borrow(&world));

        drop(world);
        drop(query);
    }

    #[test]
    #[should_panic]
    fn forgotten_query_ref_leaks_borrows() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&mut i32>::new();
        forget(query.borrow(&world));

        let _ = query.borrow(&world);
    }

    #[test]
    fn conflicting_borrow_leaves_world_in_consistent_state() {
        let mut world = World::new();

        spawn_three(&mut world);

        let res = catch_unwind(AssertUnwindSafe(|| {
            let mut query = Query::<(&i32, Option<(&mut i32, &bool)>)>::new();
            let _ = query.borrow(&world);
        }));

        assert!(res.is_err());

        let mut query = Query::<&mut i32>::new();
        let _ = query.borrow(&world);
    }

    #[test]
    fn borrows_can_be_reused() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new();
        let mut query = query.borrow(&world);

        let cnt1 = query.iter().count();
        let cnt2 = query.iter().count();

        assert_eq!(cnt1, 3);
        assert_eq!(cnt2, cnt1);
    }

    #[test]
    fn entities_can_be_queried_immutably() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&Entity>::new();
        let cnt = query.borrow(&world).iter().count();

        assert_eq!(cnt, 3);
    }

    #[test]
    #[should_panic]
    fn entities_cannot_be_queried_mutably() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&mut Entity>::new();
        let _ = query.borrow(&world).iter();
    }

    #[test]
    fn try_exposes_optional_components() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<Option<&u64>>::new();
        let cnt = query.borrow(&world).iter().count();
        let cnt_some = query.borrow(&world).iter().flatten().count();

        assert_eq!(cnt, 3);
        assert_eq!(cnt_some, 2);
    }

    #[test]
    fn with_checks_for_presence() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<With<&i32, bool>>::new();
        let sum = query.borrow(&world).iter().sum::<i32>();

        assert_eq!(sum, 42);
    }

    #[test]
    fn without_checks_for_absence() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<Without<&i32, bool>>::new();
        let sum = query.borrow(&world).iter().sum::<i32>();

        assert_eq!(sum, 23 + 1);
    }

    #[test]
    fn map_enables_access_by_entity_id() {
        let mut world = World::new();

        spawn_three(&mut world);

        let entities = Query::<&Entity>::new()
            .borrow(&world)
            .iter()
            .copied()
            .collect::<Vec<_>>();

        let mut query = Query::<&i32>::new();
        let mut query = query.borrow(&world);
        let mut query = query.map();

        for ent in entities {
            query.get_mut(ent).unwrap();
        }
    }

    #[test]
    fn fetch_ptr_has_niche() {
        assert_eq!(
            size_of::<<<(&i32, &mut f64) as QuerySpec>::Fetch as Fetch>::Ptr>(),
            size_of::<Option<<<(&i32, &mut f64) as QuerySpec>::Fetch as Fetch>::Ptr>>()
        );
    }
}
