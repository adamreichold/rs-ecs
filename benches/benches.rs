#![feature(test)]

use std::mem::swap;

extern crate test;
use test::{black_box, Bencher};

#[cfg(feature = "rayon")]
use rayon::iter::{IndexedParallelIterator, ParallelIterator};

use rs_ecs::{Entity, Query, Resources, World};

struct Pos(f32);
struct Vel(f32);

fn spawn_two<const N: usize>(world: &mut World) {
    let ent = world.alloc();
    world.insert(ent, (Pos(0.), Vel(0.), [0; 1], [0; 2], [0; 3], [(); N]));
    world.remove::<([i32; 1],)>(ent).unwrap();

    let ent = world.alloc();
    world.insert(ent, (Pos(0.), [0; 4], [0; 5], [(); N]));
    world.remove::<([i32; 4],)>(ent).unwrap();
}

fn spawn_few(world: &mut World) {
    for _ in 0..131072 / 2 {
        spawn_two::<0>(world);
    }
}

fn spawn_few_in_many_archetypes(world: &mut World) {
    for _ in 0..131072 / 2 / 8 {
        spawn_two::<0>(world);
        spawn_two::<1>(world);
        spawn_two::<2>(world);
        spawn_two::<3>(world);
        spawn_two::<4>(world);
        spawn_two::<5>(world);
        spawn_two::<6>(world);
        spawn_two::<7>(world);
    }
}

fn spawn_few_in_very_many_small_archetypes(world: &mut World) {
    for _ in 0..1024 / 2 / 32 {
        spawn_two::<0>(world);
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
    }
}

#[bench]
fn alloc_free(bencher: &mut Bencher) {
    let mut world = World::new();

    spawn_few(&mut world);

    bencher.iter(|| {
        let world = black_box(&mut world);

        let ent = world.alloc();
        let _ = world.alloc();
        world.free(ent);
    });
}

#[bench]
fn insert_remove(bencher: &mut Bencher) {
    let mut world = World::new();

    spawn_few(&mut world);

    let entities = Query::<&Entity>::new()
        .borrow(&world)
        .iter()
        .copied()
        .collect::<Vec<_>>();

    let mut entities = entities.iter().cycle();

    bencher.iter(|| {
        let world = black_box(&mut world);
        let entities = black_box(&mut entities);

        let ent = *entities.next().unwrap();

        world.remove::<(Vel,)>(ent);
        world.insert(ent, (true,));

        world.remove::<(bool,)>(ent);
        world.insert(ent, (Vel(0.0),));
    });
}

#[bench]
fn exchange(bencher: &mut Bencher) {
    let mut world = World::new();

    spawn_few(&mut world);

    let entities = Query::<&Entity>::new()
        .borrow(&world)
        .iter()
        .copied()
        .collect::<Vec<_>>();

    let mut entities = entities.iter().cycle();

    bencher.iter(|| {
        let world = black_box(&mut world);
        let entities = black_box(&mut entities);

        let ent = *entities.next().unwrap();

        world.exchange::<(Vel,), _>(ent, (true,));
        world.exchange::<(bool,), _>(ent, (Vel(0.0),));
    });
}

#[bench]
fn transfer(bencher: &mut Bencher) {
    let mut world = World::new();

    spawn_few(&mut world);

    let mut entities = Query::<&Entity>::new()
        .borrow(&world)
        .iter()
        .copied()
        .collect::<Vec<_>>();

    let mut other_world = World::new();
    let mut other_entities = Vec::new();

    bencher.iter(|| {
        let world = black_box(&mut world);
        let other_world = black_box(&mut other_world);
        let entities = black_box(&mut entities);
        let other_entities = black_box(&mut other_entities);

        if entities.is_empty() {
            swap(world, other_world);
            swap(entities, other_entities);
        }

        let ent = entities.pop().unwrap();
        let ent = world.transfer(ent, other_world);
        other_entities.push(ent);
    });
}

fn get_component(bencher: &mut Bencher, spawn: fn(&mut World)) {
    let mut world = World::new();

    spawn(&mut world);

    let entities = Query::<&Entity>::new()
        .borrow(&world)
        .iter()
        .copied()
        .collect::<Vec<_>>();

    let mut entities = entities.iter().cycle();

    bencher.iter(|| {
        let world = black_box(&mut world);
        let entities = black_box(&mut entities);

        let ent = *entities.next().unwrap();

        let mut comp = world.query_one::<(&mut Pos, Option<&Vel>)>(ent).unwrap();
        let (_pos, _vel) = comp.get_mut();
    });
}

#[bench]
fn get_component_single_archetype(bencher: &mut Bencher) {
    get_component(bencher, spawn_few);
}

#[bench]
fn get_component_many_archetypes(bencher: &mut Bencher) {
    get_component(bencher, spawn_few_in_many_archetypes);
}

#[bench]
fn get_component_very_many_small_archetypes(bencher: &mut Bencher) {
    get_component(bencher, spawn_few_in_very_many_small_archetypes);
}

fn query(bencher: &mut Bencher, spawn: fn(&mut World)) {
    let mut world = World::new();
    let mut query = Query::<(&mut Pos, &Vel)>::new();

    spawn(&mut world);

    let _ = query.borrow(&world).iter();

    bencher.iter(|| {
        let world = black_box(&world);
        let query = black_box(&mut query);

        for (pos, vel) in query.borrow(world).iter() {
            pos.0 += vel.0;
        }
    });
}

#[bench]
fn query_single_archetype(bencher: &mut Bencher) {
    query(bencher, spawn_few);
}

#[bench]
fn query_many_archetypes(bencher: &mut Bencher) {
    query(bencher, spawn_few_in_many_archetypes);
}

#[bench]
fn query_very_many_small_archetypes(bencher: &mut Bencher) {
    query(bencher, spawn_few_in_very_many_small_archetypes);
}

fn query_map(bencher: &mut Bencher, spawn: fn(&mut World)) {
    let mut world = World::new();

    spawn(&mut world);

    let entities = Query::<&Entity>::new()
        .borrow(&world)
        .iter()
        .copied()
        .collect::<Vec<_>>();

    let mut entities = entities.iter().cycle();

    let mut query = Query::<(&mut Pos, Option<&Vel>)>::default();
    let mut query = query.borrow(&world);
    let mut query = query.map();

    bencher.iter(|| {
        let entities = black_box(&mut entities);

        let ent = *entities.next().unwrap();

        let (_pos, _vel) = query.get_mut(ent).unwrap();
    });
}

#[bench]
fn query_map_single_archetype(bencher: &mut Bencher) {
    query_map(bencher, spawn_few);
}

#[bench]
fn query_map_many_archetypes(bencher: &mut Bencher) {
    query_map(bencher, spawn_few_in_many_archetypes);
}

#[bench]
fn query_map_very_many_small_archetypes(bencher: &mut Bencher) {
    query_map(bencher, spawn_few_in_very_many_small_archetypes);
}

fn query_for_each(bencher: &mut Bencher, spawn: fn(&mut World)) {
    let mut world = World::new();
    let mut query = Query::<(&mut Pos, &Vel)>::new();

    spawn(&mut world);

    let _ = query.borrow(&world).iter();

    bencher.iter(|| {
        let world = black_box(&world);
        let query = black_box(&mut query);

        query.borrow(world).for_each(|(pos, vel)| {
            pos.0 += vel.0;
        });
    });
}

#[bench]
fn query_for_each_single_archetype(bencher: &mut Bencher) {
    query_for_each(bencher, spawn_few);
}

#[bench]
fn query_for_each_many_archetypes(bencher: &mut Bencher) {
    query_for_each(bencher, spawn_few_in_many_archetypes);
}

#[bench]
fn query_for_each_very_many_small_archetypes(bencher: &mut Bencher) {
    query_for_each(bencher, spawn_few_in_very_many_small_archetypes);
}

#[bench]
fn get_resource(bencher: &mut Bencher) {
    let mut resources = Resources::new();

    resources.insert(23);
    resources.insert(42.0);

    bencher.iter(|| {
        let _i32 = resources.get_mut::<i32>();
        let _f64 = resources.get::<f64>();
    });
}

#[cfg(feature = "rayon")]
fn query_parallel(bencher: &mut Bencher, spawn: fn(&mut World)) {
    let mut world = World::new();
    let mut query = Query::<(&mut Pos, &Vel)>::new();

    spawn(&mut world);

    let _ = query.borrow(&world).iter();

    bencher.iter(|| {
        let world = black_box(&world);
        let query = black_box(&mut query);

        query
            .borrow(world)
            .par_iter()
            .with_min_len(1024)
            .for_each(|(pos, vel)| {
                pos.0 += vel.0;
            });
    });
}

#[cfg(feature = "rayon")]
#[bench]
fn query_parallel_single_archetype(bencher: &mut Bencher) {
    query_parallel(bencher, spawn_few);
}

#[cfg(feature = "rayon")]
#[bench]
fn query_parallel_many_archetypes(bencher: &mut Bencher) {
    query_parallel(bencher, spawn_few_in_many_archetypes);
}

#[cfg(feature = "rayon")]
#[bench]
fn query_parallel_very_many_small_archetypes(bencher: &mut Bencher) {
    query_parallel(bencher, spawn_few_in_very_many_small_archetypes);
}
