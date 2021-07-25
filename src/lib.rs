//! A reasonably simple entity component system (ECS).
//!
//! The design is based on [hecs](https://github.com/Ralith/hecs) but it is not thread-safe
//! and has a significantly reduced API surface.
//!
//! # Example
//!
//! ```
//! # use rs_ecs::*;
//!
//! let mut world = World::new();
//!
//! let entity = world.alloc();
//! world.insert(entity, (42_u32, true));
//!
//! let entity = world.alloc();
//! world.insert(entity, (23_u32, "hello".to_string()));
//!
//! for number in Query::<&u32>::new().borrow(&world).iter() {
//!     println!("{}", number);
//! }
//!
//! for (_entity, number, string) in Query::<(&Entity, &u32, &String)>::new().borrow(&world).iter() {
//!     println!("{}, {}", string, number);
//! }
//! ```

#![warn(missing_docs)]

mod archetype;
mod query;
#[cfg(feature = "rayon")]
mod rayon;
mod resources;
mod world;

pub use crate::{
    archetype::{Comp, CompMut},
    query::{Query, QueryIter, QueryMap, QueryRef, QuerySpec, With, Without},
    resources::{Res, ResMut, Resources},
    world::{Entity, World},
};
