use std::iter::FusedIterator;
use std::mem::replace;

use rayon::iter::{
    plumbing::{bridge, Consumer, Folder, Producer, ProducerCallback, UnindexedConsumer},
    IndexedParallelIterator, ParallelIterator,
};

use crate::{
    archetype::Archetype,
    query::{Fetch, QuerySpec},
};

/// Used to iterate through the entities which match a certain [Query][crate::query::Query] in parallel.
pub struct QueryParIter<'q, S>
where
    S: QuerySpec,
{
    types: &'q [(u16, <S::Fetch as Fetch<'q>>::Ty)],
    archetypes: &'q [Archetype],
    idx: u32,
    len: u32,
}

unsafe impl<'q, S> Send for QueryParIter<'q, S>
where
    S: QuerySpec,
    <S::Fetch as Fetch<'q>>::Ty: Send + Sync,
{
}

impl<'q, S> QueryParIter<'q, S>
where
    S: QuerySpec,
{
    pub(crate) fn new(
        types: &'q [(u16, <S::Fetch as Fetch<'q>>::Ty)],
        archetypes: &'q [Archetype],
    ) -> Self {
        let len = types
            .iter()
            .map(|(idx, _ty)| archetypes[*idx as usize].len())
            .sum();

        Self {
            types,
            archetypes,
            idx: 0,
            len,
        }
    }
}

impl<'q, S> ParallelIterator for QueryParIter<'q, S>
where
    S: QuerySpec,
    <S::Fetch as Fetch<'q>>::Ty: Send + Sync,
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
        Some(self.len())
    }
}

impl<'q, S> IndexedParallelIterator for QueryParIter<'q, S>
where
    S: QuerySpec,
    <S::Fetch as Fetch<'q>>::Ty: Send + Sync,
    <S::Fetch as Fetch<'q>>::Item: Send,
{
    fn drive<C>(self, consumer: C) -> C::Result
    where
        C: Consumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn len(&self) -> usize {
        (self.len - self.idx) as usize
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        callback.callback(self)
    }
}

impl<'q, S> Producer for QueryParIter<'q, S>
where
    S: QuerySpec,
    <S::Fetch as Fetch<'q>>::Ty: Send + Sync,
    <S::Fetch as Fetch<'q>>::Item: Send,
{
    type Item = <S::Fetch as Fetch<'q>>::Item;
    type IntoIter = QueryParIterIntoIter<'q, S>;

    fn into_iter(self) -> Self::IntoIter {
        let mut sum = 0;

        let mut first = 0;
        let mut last = 0;

        let mut idx = 0;
        let mut len = 0;
        let mut ptr = S::Fetch::dangling();

        let idx_back = 0;
        let mut len_back = 0;
        let mut ptr_back = S::Fetch::dangling();

        for (pos, (archetype_idx, ty)) in self.types.iter().enumerate() {
            let archetype = &self.archetypes[*archetype_idx as usize];

            if archetype.len() == 0 {
                continue;
            }

            sum += archetype.len();

            if self.idx >= sum {
                continue;
            }

            if sum - self.idx <= archetype.len() {
                first = pos + 1;

                idx = archetype.len() - (sum - self.idx);
                len = archetype.len();
                ptr = unsafe { S::Fetch::base_pointer(archetype, *ty) };

                if self.len <= sum {
                    last = first;

                    len -= sum - self.len;

                    break;
                }
            }

            if self.len <= sum {
                last = pos;

                len_back = archetype.len() - (sum - self.len);
                ptr_back = unsafe { S::Fetch::base_pointer(archetype, *ty) };

                break;
            }
        }

        let types = &self.types[first..last];

        QueryParIterIntoIter {
            types,
            archetypes: self.archetypes,
            idx,
            len,
            ptr,
            idx_back,
            len_back,
            ptr_back,
        }
    }

    fn fold_with<F>(self, mut folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        let mut sum = 0;

        for (archetype_idx, ty) in self.types {
            if self.len <= sum {
                break;
            }

            let archetype = &self.archetypes[*archetype_idx as usize];

            if archetype.len() == 0 {
                continue;
            }

            sum += archetype.len();

            if self.idx >= sum {
                continue;
            }

            let mut idx = 0;
            let mut len = archetype.len();
            let ptr = unsafe { S::Fetch::base_pointer(archetype, *ty) };

            if sum - self.idx < len {
                idx = len - (sum - self.idx);
            }

            if self.len < sum {
                len -= sum - self.len;
            }

            while idx != len {
                let val = unsafe { S::Fetch::deref(ptr, idx) };
                idx += 1;

                folder = folder.consume(val);
                if folder.full() {
                    break;
                }
            }
        }

        folder
    }

    fn split_at(self, mid: usize) -> (Self, Self) {
        let mid = self.idx + mid as u32;

        let lhs = Self {
            types: self.types,
            archetypes: self.archetypes,
            idx: self.idx,
            len: mid,
        };

        let rhs = Self {
            types: self.types,
            archetypes: self.archetypes,
            idx: mid,
            len: self.len,
        };

        (lhs, rhs)
    }
}

pub struct QueryParIterIntoIter<'q, S>
where
    S: QuerySpec,
{
    types: &'q [(u16, <S::Fetch as Fetch<'q>>::Ty)],
    archetypes: &'q [Archetype],
    idx: u32,
    len: u32,
    ptr: <S::Fetch as Fetch<'q>>::Ptr,
    idx_back: u32,
    len_back: u32,
    ptr_back: <S::Fetch as Fetch<'q>>::Ptr,
}

impl<'q, S> Iterator for QueryParIterIntoIter<'q, S>
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
                match self.types.split_first() {
                    Some(((idx, ty), rest)) => {
                        self.types = rest;

                        let archetype = &self.archetypes[*idx as usize];
                        self.idx = 0;
                        self.len = archetype.len();
                        self.ptr = unsafe { S::Fetch::base_pointer(archetype, *ty) };
                    }
                    None => {
                        if self.idx_back == self.len_back {
                            return None;
                        } else {
                            self.idx = replace(&mut self.idx_back, 0);
                            self.len = replace(&mut self.len_back, 0);
                            self.ptr = replace(&mut self.ptr_back, S::Fetch::dangling());
                        }
                    }
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<S> DoubleEndedIterator for QueryParIterIntoIter<'_, S>
where
    S: QuerySpec,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            if self.idx_back != self.len_back {
                let val = unsafe { S::Fetch::deref(self.ptr, self.len_back - 1) };
                self.len_back -= 1;
                return Some(val);
            } else {
                match self.types.split_last() {
                    Some(((idx, ty), rest)) => {
                        self.types = rest;

                        let archetype = &self.archetypes[*idx as usize];
                        self.idx_back = 0;
                        self.len_back = archetype.len();
                        self.ptr_back = unsafe { S::Fetch::base_pointer(archetype, *ty) };
                    }
                    None => {
                        if self.idx == self.len {
                            return None;
                        } else {
                            self.idx_back = replace(&mut self.idx, 0);
                            self.len_back = replace(&mut self.len, 0);
                            self.ptr_back = replace(&mut self.ptr, S::Fetch::dangling());
                        }
                    }
                }
            }
        }
    }
}

impl<S> ExactSizeIterator for QueryParIterIntoIter<'_, S>
where
    S: QuerySpec,
{
    fn len(&self) -> usize {
        let len = self
            .types
            .iter()
            .map(|(idx, _)| self.archetypes[*idx as usize].len())
            .sum::<u32>()
            + self.len
            - self.idx;
        len as usize
    }
}

impl<S> FusedIterator for QueryParIterIntoIter<'_, S> where S: QuerySpec {}

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
