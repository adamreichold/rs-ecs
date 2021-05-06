# rs-ecs

A reasonably simple entity component system (ECS) developed for use in the simulation models of [project group EcoEpi](https://ecoepi.eu/) at the [Helmholtz Centre for Environmental Research](https://www.ufz.de/). The design is based on [hecs](https://github.com/Ralith/hecs) but it drops all optimisations which require additional API surface. Furthermore, it is _not_ thread-safe, uses prepared queries only and adds a type map used to hold resources.

## License

Licensed under

 * [Apache License, Version 2.0](LICENSE-APACHE) or
 * [MIT license](LICENSE-MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
