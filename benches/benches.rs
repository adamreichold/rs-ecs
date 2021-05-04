#![feature(test)]

extern crate test;
use test::{black_box, Bencher};

use rs_ecs::{Query, World};

struct Pos(f32);
struct Vel(f32);

#[bench]
fn alloc_free(bencher: &mut Bencher) {
    let mut world = World::default();

    bencher.iter(|| {
        let world = black_box(&mut world);

        let ent = world.alloc();
        let _ = world.alloc();
        world.free(ent);
    })
}

#[bench]
fn insert_remove(bencher: &mut Bencher) {
    let mut world = World::default();

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

#[bench]
fn query(bencher: &mut Bencher) {
    let mut world = World::default();
    let mut query = Query::<(&mut Pos, &Vel)>::default();

    for _ in 0..131072 {
        let ent = world.alloc();
        world.insert(ent, (Pos(0.), Vel(0.)));
    }

    bencher.iter(|| {
        let world = black_box(&world);
        let query = black_box(&mut query);

        for (pos, vel) in query.iter(world) {
            pos.0 += vel.0;
        }
    });
}
