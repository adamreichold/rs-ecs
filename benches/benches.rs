#![feature(test)]

extern crate test;
use test::{black_box, Bencher};

use rs_ecs::{Query, World};

struct Pos(f32);
struct Vel(f32);

#[bench]
fn alloc_free(bencher: &mut Bencher) {
    let mut world = World::new();

    bencher.iter(|| {
        let world = black_box(&mut world);

        let ent = world.alloc();
        let _ = world.alloc();
        world.free(ent);
    })
}

#[bench]
fn insert_remove(bencher: &mut Bencher) {
    let mut world = World::new();

    let mut entities = Vec::new();
    let mut entity_idx = 0;

    for _ in 0..1_024 {
        let ent = world.alloc();
        world.insert(ent, (Pos(0.), Vel(0.)));
        entities.push(ent);
    }

    bencher.iter(|| {
        let world = black_box(&mut world);
        let entities = black_box(&entities);
        let entity_idx = black_box(&mut entity_idx);

        let ent = entities[*entity_idx];
        *entity_idx = (*entity_idx + 1) % 1024;

        world.remove::<(Vel,)>(ent);
        world.insert(ent, (Vel(0.0),));
    })
}

fn spawn_two<const N: usize>(world: &mut World) {
    let ent = world.alloc();
    world.insert(ent, (Pos(0.), Vel(0.), [0; 1], [0; 2], [0; 3], [(); N]));

    let ent = world.alloc();
    world.insert(ent, (Pos(0.), [0; 4], [0; 5], [(); N]));
}

#[bench]
fn query_single_archetype(bencher: &mut Bencher) {
    let mut world = World::new();
    let mut query = Query::<(&mut Pos, &Vel)>::new();

    for _ in 0..1024 / 2 {
        spawn_two::<0>(&mut world);
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
