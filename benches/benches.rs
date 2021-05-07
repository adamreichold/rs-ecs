#![feature(test)]

extern crate test;
use test::{black_box, Bencher};

use rs_ecs::{Entity, Query, Resources, World};

struct Pos(f32);
struct Vel(f32);

fn spawn_two<const N: usize>(world: &mut World) {
    let ent = world.alloc();
    world.insert(ent, (Pos(0.), Vel(0.), [0; 1], [0; 2], [0; 3], [(); N]));

    let ent = world.alloc();
    world.insert(ent, (Pos(0.), [0; 4], [0; 5], [(); N]));
}

fn spawn_few(world: &mut World) {
    for _ in 0..1024 / 2 {
        spawn_two::<0>(world);
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
        .iter(&world)
        .copied()
        .collect::<Vec<_>>();

    let mut entities = entities.iter().cycle();

    bencher.iter(|| {
        let world = black_box(&mut world);
        let entities = black_box(&mut entities);

        let ent = *entities.next().unwrap();

        world.remove::<(Pos,)>(ent);
        world.remove::<(Vel,)>(ent);

        world.insert(ent, (Vel(0.0),));
        world.insert(ent, (Pos(0.0),));
    });
}

#[bench]
fn get_component(bencher: &mut Bencher) {
    let mut world = World::new();

    spawn_few(&mut world);

    let entities = Query::<&Entity>::new()
        .iter(&world)
        .copied()
        .collect::<Vec<_>>();

    let mut entities = entities.iter().cycle();

    bencher.iter(|| {
        let world = black_box(&mut world);
        let entities = black_box(&mut entities);

        let ent = *entities.next().unwrap();

        let _pos = world.get_mut::<Pos>(ent).unwrap();
        let _vel = world.get::<Vel>(ent);
    });
}

#[bench]
fn query_single_archetype(bencher: &mut Bencher) {
    let mut world = World::new();
    let mut query = Query::<(&mut Pos, &Vel)>::new();

    spawn_few(&mut world);

    let _ = query.iter(&world);

    bencher.iter(|| {
        let world = black_box(&world);
        let query = black_box(&mut query);

        for (pos, vel) in query.iter(world) {
            pos.0 += vel.0;
        }
    });
}

#[bench]
fn query_many_archetypes(bencher: &mut Bencher) {
    let mut world = World::new();
    let mut query = Query::<(&mut Pos, &Vel)>::new();

    for _ in 0..1024 / 2 / 8 {
        spawn_two::<0>(&mut world);
        spawn_two::<1>(&mut world);
        spawn_two::<2>(&mut world);
        spawn_two::<3>(&mut world);
        spawn_two::<4>(&mut world);
        spawn_two::<5>(&mut world);
        spawn_two::<6>(&mut world);
        spawn_two::<7>(&mut world);
    }

    let _ = query.iter(&world);

    bencher.iter(|| {
        let world = black_box(&world);
        let query = black_box(&mut query);

        for (pos, vel) in query.iter(world) {
            pos.0 += vel.0;
        }
    });
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
