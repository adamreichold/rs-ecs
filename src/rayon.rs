use std::iter::FusedIterator;

use rayon::iter::{
    plumbing::{bridge, Consumer, Producer, ProducerCallback, UnindexedConsumer},
    IndexedParallelIterator, ParallelIterator,
};

use crate::{
    archetype::Archetype,
    query::{Fetch, QuerySpec},
};

pub struct ArchetypeIterFactory<'q>(&'q [Archetype]);

unsafe impl Send for ArchetypeIterFactory<'_> {}

unsafe impl Sync for ArchetypeIterFactory<'_> {}

impl<'q> ArchetypeIterFactory<'q> {
    pub fn new(archetypes: &'q [Archetype]) -> Self {
        Self(archetypes)
    }

    pub unsafe fn iter<S>(
        &self,
        idx: u16,
        ty: <S::Fetch as Fetch<'q>>::Ty,
    ) -> impl IndexedParallelIterator<Item = <S::Fetch as Fetch<'q>>::Item> + 'q
    where
        S: QuerySpec + 'q,
        <S::Fetch as Fetch<'q>>::Item: Send,
    {
        let archetype = &self.0[idx as usize];

        ArchetypeIter::<'q, S> {
            idx: 0,
            len: archetype.len(),
            ptr: S::Fetch::base_pointer(archetype, ty),
        }
    }
}

struct ArchetypeIter<'q, S>
where
    S: QuerySpec,
{
    idx: u32,
    len: u32,
    ptr: <S::Fetch as Fetch<'q>>::Ptr,
}

unsafe impl<S> Send for ArchetypeIter<'_, S> where S: QuerySpec {}

impl<'q, S> Iterator for ArchetypeIter<'q, S>
where
    S: QuerySpec,
{
    type Item = <S::Fetch as Fetch<'q>>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx != self.len {
            let val = unsafe { S::Fetch::deref(self.ptr, self.idx) };
            self.idx += 1;
            Some(val)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'q, S> DoubleEndedIterator for ArchetypeIter<'q, S>
where
    S: QuerySpec,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.idx != self.len {
            let val = unsafe { S::Fetch::deref(self.ptr, self.len - 1) };
            self.len -= 1;
            Some(val)
        } else {
            None
        }
    }
}

impl<S> FusedIterator for ArchetypeIter<'_, S> where S: QuerySpec {}

impl<S> ExactSizeIterator for ArchetypeIter<'_, S>
where
    S: QuerySpec,
{
    fn len(&self) -> usize {
        (self.len - self.idx) as usize
    }
}

impl<'q, S> ParallelIterator for ArchetypeIter<'q, S>
where
    S: QuerySpec,
    <S::Fetch as Fetch<'q>>::Item: Send,
{
    type Item = <S::Fetch as Fetch<'q>>::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(ExactSizeIterator::len(self))
    }
}

impl<'q, S> IndexedParallelIterator for ArchetypeIter<'q, S>
where
    S: QuerySpec,
    <S::Fetch as Fetch<'q>>::Item: Send,
{
    fn drive<C>(self, consumer: C) -> C::Result
    where
        C: Consumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn len(&self) -> usize {
        ExactSizeIterator::len(self)
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        callback.callback(self)
    }
}

impl<'q, S> Producer for ArchetypeIter<'q, S>
where
    S: QuerySpec,
    <S::Fetch as Fetch<'q>>::Item: Send,
{
    type Item = <S::Fetch as Fetch<'q>>::Item;
    type IntoIter = Self;

    fn into_iter(self) -> Self::IntoIter {
        self
    }

    fn split_at(self, mid: usize) -> (Self, Self) {
        let len = ExactSizeIterator::len(&self);
        assert!(mid <= len);

        let mid = self.idx + mid as u32;

        let left = ArchetypeIter {
            idx: self.idx,
            len: mid,
            ptr: self.ptr,
        };

        let right = ArchetypeIter {
            idx: mid,
            len: self.len,
            ptr: self.ptr,
        };

        (left, right)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{query::Query, world::World};

    struct Pos(f32);
    struct Vel(f32);

    fn spawn_two<const N: usize>(world: &mut World) {
        let ent = world.alloc();
        world.insert(ent, (Pos(0.), Vel(0.), [N; 1], [0; 2], [0; 3], [(); N]));
        world.remove::<([i32; 2],)>(ent).unwrap();

        let ent = world.alloc();
        world.insert(ent, (Pos(0.), [0; 4], [0; 5], [(); N]));
        world.remove::<([i32; 4],)>(ent).unwrap();
    }

    fn spawn_few(world: &mut World) {
        for _ in 0..131072 / 2 {
            spawn_two::<1>(world);
        }
    }

    fn spawn_few_in_many_archetypes(world: &mut World) {
        for _ in 0..131072 / 2 / 8 {
            spawn_two::<1>(world);
            spawn_two::<2>(world);
            spawn_two::<3>(world);
            spawn_two::<4>(world);
            spawn_two::<5>(world);
            spawn_two::<6>(world);
            spawn_two::<7>(world);
            spawn_two::<8>(world);
        }
    }

    fn spawn_few_in_very_many_small_archetypes(world: &mut World) {
        for _ in 0..1024 / 2 / 32 {
            spawn_two::<1>(world);
            spawn_two::<2>(world);
            spawn_two::<3>(world);
            spawn_two::<4>(world);
            spawn_two::<5>(world);
            spawn_two::<6>(world);
            spawn_two::<7>(world);
            spawn_two::<8>(world);
            spawn_two::<9>(world);
            spawn_two::<10>(world);
            spawn_two::<11>(world);
            spawn_two::<12>(world);
            spawn_two::<13>(world);
            spawn_two::<14>(world);
            spawn_two::<15>(world);
            spawn_two::<16>(world);
            spawn_two::<17>(world);
            spawn_two::<18>(world);
            spawn_two::<19>(world);
            spawn_two::<20>(world);
            spawn_two::<21>(world);
            spawn_two::<22>(world);
            spawn_two::<23>(world);
            spawn_two::<24>(world);
            spawn_two::<25>(world);
            spawn_two::<26>(world);
            spawn_two::<27>(world);
            spawn_two::<28>(world);
            spawn_two::<29>(world);
            spawn_two::<30>(world);
            spawn_two::<31>(world);
            spawn_two::<32>(world);
        }
    }

    #[test]
    fn it_works_with_a_single_archetype() {
        let mut world = World::new();

        spawn_few(&mut world);

        let mut query = Query::<(&mut Pos, &Vel, &[usize; 1])>::new();

        let sum = query
            .borrow(&world)
            .par_iter()
            .map(|(_pos, _vel, comp)| comp[0])
            .sum::<usize>();

        assert_eq!(sum, 65_536)
    }

    #[test]
    fn it_works_with_many_archetypes() {
        let mut world = World::new();

        spawn_few_in_many_archetypes(&mut world);

        let mut query = Query::<(&mut Pos, &Vel, &[usize; 1])>::new();

        let sum = query
            .borrow(&world)
            .par_iter()
            .map(|(_pos, _vel, comp)| comp[0])
            .sum::<usize>();

        assert_eq!(sum, 294_912)
    }

    #[test]
    fn it_works_with_very_many_small_archetypes() {
        let mut world = World::new();

        spawn_few_in_very_many_small_archetypes(&mut world);

        let mut query = Query::<(&mut Pos, &Vel, &[usize; 1])>::new();

        let sum = query
            .borrow(&world)
            .par_iter()
            .map(|(_pos, _vel, comp)| comp[0])
            .sum::<usize>();

        assert_eq!(sum, 8_448)
    }
}
