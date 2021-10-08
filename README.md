# rs-ecs

[![crates.io](https://img.shields.io/crates/v/rs-ecs.svg)](https://crates.io/crates/rs-ecs)
[![docs.rs](https://docs.rs/rs-ecs/badge.svg)](https://docs.rs/rs-ecs)
[![github.com](https://github.com/adamreichold/rs-ecs/actions/workflows/test.yaml/badge.svg)](https://github.com/adamreichold/rs-ecs/actions/workflows/test.yaml)

A reasonably simple entity component system (ECS) developed for use in the simulation models of [project group EcoEpi](https://ecoepi.eu/) at the [Helmholtz Centre for Environmental Research](https://www.ufz.de/). The design is based on [hecs](https://github.com/Ralith/hecs) but has a significantly reduced API surface.

It also has a few changes and additions specific to our use case:

* It is not thread-safe as the execution of single-threaded simulations is trivially deterministic. Additionally, running multiple instances of these in parallel often gives the highest throughput.
* It supports amortised random access to query results by entity identifier using the [`QueryRef::map` method](https://docs.rs/rs-ecs/*/rs_ecs/struct.QueryRef.html#method.map). This can be useful to efficiently traverse graph-like relations between entities.
* Entities can be transferred between worlds without serialisation using the [`World::transfer` method](https://docs.rs/rs-ecs/*/rs_ecs/struct.World.html#method.transfer). We use this to completely remove entities from the simulation while keeping their full dynamic state around for later inspection.
* While queries must be dispatched from a single thread, their results can be iterated using multiple threads via the [`QueryRef::par_iter` method](https://docs.rs/rs-ecs/*/rs_ecs/struct.QueryRef.html#method.par_iter). The method is optional, implemented using [Rayon](https://github.com/rayon-rs/rayon) and enabled by the `rayon` Cargo feature.

## License

Licensed under

 * [Apache License, Version 2.0](LICENSE-APACHE) or
 * [MIT license](LICENSE-MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
