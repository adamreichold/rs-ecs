use std::any::TypeId;
use std::slice::from_raw_parts;

use erased_serde::{serialize as erased_serialize, Serialize as ErasedSerialize};
use serde::ser::{Serialize, SerializeMap, Serializer};

use crate::resources::TypeIdMap;
use crate::world::Entity;

/// TODO
pub struct ComponentSerializer {
    keys: TypeIdMap<&'static str>,
    serialize_fns: TypeIdMap<SerializeFn>,
}

type SerializeFn = unsafe fn(*mut u8, u32, &mut dyn FnMut(&dyn ErasedSerialize));

impl ComponentSerializer {
    /// TODO
    pub fn new() -> Self {
        let mut _self = Self {
            keys: Default::default(),
            serialize_fns: Default::default(),
        };

        unsafe {
            _self.register::<Entity>("Entity");
        }

        _self
    }
}

impl Default for ComponentSerializer {
    fn default() -> Self {
        Self::new()
    }
}

impl ComponentSerializer {
    /// TODO
    ///
    /// # Safety
    ///
    /// TODO
    ///
    pub unsafe fn register<C>(&mut self, key: &'static str)
    where
        C: Serialize + 'static,
    {
        unsafe fn serialize<C>(ptr: *mut u8, len: u32, cont: &mut dyn FnMut(&dyn ErasedSerialize))
        where
            C: Serialize + 'static,
        {
            let vals = from_raw_parts(ptr.cast::<C>(), len as usize);

            cont(&vals);
        }

        for &key1 in self.keys.values() {
            assert_ne!(key, key1, "Keys must be unique");
        }

        let id = TypeId::of::<C>();
        self.keys.insert(id, key);
        self.serialize_fns.insert(id, serialize::<C>);
    }

    pub(crate) unsafe fn serialize_component<S>(
        &self,
        ty: &TypeId,
        base_pointer: *mut u8,
        len: u32,
        serializer: &mut S,
    ) -> Result<(), S::Error>
    where
        S: SerializeMap,
    {
        struct Eraser {
            base_pointer: *mut u8,
            len: u32,
            serialize: SerializeFn,
        }

        impl Serialize for Eraser {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                let mut serializer = Some(serializer);
                let mut result = None;

                unsafe {
                    (self.serialize)(self.base_pointer, self.len, &mut |serialize| {
                        result = Some(erased_serialize(serialize, serializer.take().unwrap()));
                    });
                }

                result.unwrap()
            }
        }

        let &key = self
            .keys
            .get(ty)
            .expect("Component was not registered with serializer");

        let &serialize = self.serialize_fns.get(ty).unwrap();

        serializer.serialize_entry(
            key,
            &Eraser {
                base_pointer,
                len,
                serialize,
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::world::{World, WorldSerializer};

    use serde_json::{json, to_value};

    #[test]
    fn serialize_world() {
        let mut world = World::new();

        let ent = world.alloc();
        world.insert(ent, (42_i32, true, "foo".to_owned()));

        let ent = world.alloc();
        world.insert(ent, (23_i32, "bar".to_owned()));

        let mut serializer = ComponentSerializer::new();

        unsafe {
            serializer.register::<i32>("i32");
            serializer.register::<bool>("bool");
            serializer.register::<String>("String");
        }

        let value = to_value(WorldSerializer {
            world: &world,
            serializer: &serializer,
        })
        .unwrap();

        assert_eq!(
            value,
            json!({
                "entities": [
                    {"gen": 1, "ty": 1, "idx": 0},
                    {"gen": 1, "ty": 2, "idx": 0},
                ],
                "free_list": [],
                "archetypes": [
                    {
                        "Entity": [{"gen": 1, "id": 0}],
                        "String": ["foo"],
                        "bool": [true],
                        "i32": [42],
                    },
                    {
                        "Entity": [{"gen": 1, "id": 1}],
                        "String": ["bar"],
                        "i32": [23],
                    },
                ],
            })
        );
    }
}
