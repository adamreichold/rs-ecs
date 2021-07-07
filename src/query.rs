use std::any::TypeId;
use std::cell::{Ref, RefMut};
use std::marker::PhantomData;
use std::mem::{transmute, ManuallyDrop};
use std::ptr::NonNull;
use std::slice::Iter;

use crate::{
    archetype::Archetype,
    world::{Entity, EntityMetadata, World},
};

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
    tag_gen: (u32, u32),
    types: Vec<(usize, <S::Fetch as Fetch<'static>>::Ty)>,
    refs: Vec<ManuallyDrop<<S::Fetch as Fetch<'static>>::Ref>>,
    ptrs: Vec<(u32, <S::Fetch as Fetch<'static>>::Ptr)>,
}

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

        let types: &'w [(usize, <S::Fetch as Fetch<'w>>::Ty)] = unsafe { transmute(&*self.types) };
        let refs: &'w mut Vec<<S::Fetch as Fetch<'w>>::Ref> = unsafe { transmute(&mut self.refs) };
        let ptrs: &'w mut Vec<(u32, <S::Fetch as Fetch<'w>>::Ptr)> =
            unsafe { transmute(&mut self.ptrs) };

        for (idx, ty) in types {
            let archetype = &world.archetypes[*idx];

            if archetype.len() != 0 {
                refs.push(unsafe { S::Fetch::borrow(archetype, *ty) });
            }
        }

        QueryRef {
            world,
            types,
            refs,
            ptrs,
        }
    }

    #[cold]
    #[inline(never)]
    fn find(&mut self, world: &World) {
        self.types.clear();

        for (idx, archetype) in world.archetypes.iter().enumerate() {
            if let Some(ty) = S::Fetch::find(archetype) {
                self.types.push((idx, ty));
            }
        }

        self.tag_gen = world.tag_gen();
    }

    /// Narrow down a query to entities that have a certain component,
    /// without borrowing that component.
    ///
    /// For use with prepared queries, see [With].
    ///
    /// # Examples
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let query = Query::<(&i32,)>::new().with::<bool>();
    /// ```
    pub fn with<C>(self) -> Query<With<S, C>>
    where
        C: 'static,
    {
        Query::new()
    }

    /// Narrow down a query to entities that do not have a certain component.
    ///
    /// For use with prepared queries, see [Without].
    ///
    /// # Examples
    ///
    /// ```
    /// # use rs_ecs::*;
    /// let query = Query::<(&i32,)>::new().without::<bool>();
    /// ```
    pub fn without<C>(self) -> Query<Without<S, C>>
    where
        C: 'static,
    {
        Query::new()
    }
}

/// Borrow of the [World] for a [Query]. Required to obtain an iterator.
pub struct QueryRef<'w, S>
where
    S: QuerySpec,
{
    world: &'w World,
    types: &'w [(usize, <S::Fetch as Fetch<'w>>::Ty)],
    refs: &'w mut Vec<<S::Fetch as Fetch<'w>>::Ref>,
    ptrs: &'w mut Vec<(u32, <S::Fetch as Fetch<'w>>::Ptr)>,
}

impl<S> QueryRef<'_, S>
where
    S: QuerySpec,
{
    /// Create an iterator over the entities matching the query.
    pub fn iter<'q>(&'q mut self) -> QueryIter<'q, S> {
        let types: &'q [(usize, <S::Fetch as Fetch<'q>>::Ty)] = unsafe { transmute(self.types) };

        QueryIter {
            types: types.iter(),
            archetypes: &self.world.archetypes,
            idx: 0,
            len: 0,
            ptr: S::Fetch::dangling(),
        }
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
    /// let (i, f) = query.get(entity).unwrap();
    ///
    /// assert_eq!(*i, 42);
    /// assert_eq!(*f, 1.0);
    /// ```
    pub fn map<'q>(&'q mut self) -> QueryMap<'q, S> {
        let types: &'q [(usize, <S::Fetch as Fetch<'q>>::Ty)] = unsafe { transmute(self.types) };
        let ptrs: &'q mut Vec<(u32, <S::Fetch as Fetch<'q>>::Ptr)> =
            unsafe { transmute(&mut *self.ptrs) };

        ptrs.clear();

        ptrs.resize(self.world.archetypes.len(), (0, S::Fetch::dangling()));

        for (idx, ty) in types {
            let archetype = &self.world.archetypes[*idx];

            let len = archetype.len();
            let ptr = unsafe { S::Fetch::base_pointer(archetype, *ty) };

            ptrs[*idx] = (len, ptr);
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
            .map(|(idx, _)| self.archetypes[*idx].len())
            .sum::<u32>()
            + self.len
            - self.idx;
        len as usize
    }
}

/// Provides random access to the entities which match a certain [Query].
pub struct QueryMap<'q, S>
where
    S: QuerySpec,
{
    entities: &'q [EntityMetadata],
    ptrs: &'q [(u32, <S::Fetch as Fetch<'q>>::Ptr)],
}

impl<'q, S> QueryMap<'q, S>
where
    S: QuerySpec,
{
    /// Access the queried components of the given [Entity]
    pub fn get<'m>(&'m mut self, ent: Entity) -> Option<<S::Fetch as Fetch<'m>>::Item> {
        let meta = self.entities[ent.id as usize];
        assert_eq!(ent.gen, meta.gen, "Entity is stale");

        let (len, ptr): &'m (u32, <S::Fetch as Fetch<'m>>::Ptr) =
            unsafe { transmute(&self.ptrs[meta.ty as usize]) };

        if meta.idx < *len {
            let val = unsafe { S::Fetch::deref(*ptr, meta.idx) };

            Some(val)
        } else {
            None
        }
    }
}

/// Type level specification of a query for a certain set of components.
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
    unsafe fn base_pointer(archetype: &'q Archetype, ty: Self::Ty) -> Self::Ptr;

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
    type Ptr = NonNull<C>;

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

/// A query specification to iterate over entities with a certain component,
/// but without borrowing that component.
///
/// See also [Query::with()]
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

/// A query specification to iterate over entities without a certain component.
///
/// See also [Query::without()]
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
    };
}

impl_fetch_for_tuples!(A, B, C, D, E, F, G, H, I, J);

#[cfg(test)]
mod tests {
    use super::*;

    use std::mem::{forget, size_of};

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

        let mut query = Query::<&i32>::new().with::<bool>();
        let sum = query.borrow(&world).iter().sum::<i32>();

        assert_eq!(sum, 42);
    }

    #[test]
    fn without_checks_for_absence() {
        let mut world = World::new();

        spawn_three(&mut world);

        let mut query = Query::<&i32>::new().without::<bool>();
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
            query.get(ent).unwrap();
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
