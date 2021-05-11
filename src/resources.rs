use std::any::{type_name, Any, TypeId};
use std::cell::{Ref, RefCell, RefMut};
use std::collections::hash_map::{Entry, HashMap};
use std::hash::{BuildHasherDefault, Hasher};
use std::ops::{Deref, DerefMut};

/// A type map for holding resources.
///
/// Resources replace global variables and my be accessed by systems that know their type.
///
/// # Examples
///
/// ```
/// # use rs_ecs::*;
/// struct MyResource(u32);
///
/// let mut resources = Resources::new();
///
/// // Insert multiple resources
/// resources.insert(42_u32);
/// resources.insert(MyResource(0));
///
/// // Borrow a resource immutably
/// let my_res = resources.get::<MyResource>();
///
/// // Borrow a resource mutably
/// let mut u32_res = resources.get_mut::<u32>();
/// *u32_res += 1;
/// ```
pub struct Resources(HashMap<TypeId, RefCell<Box<dyn Any>>, BuildHasherDefault<TypeIdHasher>>);

impl Default for Resources {
    /// Create an empty resources map. Synonym for [Self::new()].
    fn default() -> Self {
        Self::new()
    }
}

impl Resources {
    /// Create an empty resources map. Synonym for [Self::default()].
    pub fn new() -> Self {
        Self(Default::default())
    }
}

impl Resources {
    /// Insert a resource.
    ///
    /// # Panics
    ///
    /// Panics if a resource of the same type is already present.
    pub fn insert<R>(&mut self, res: R)
    where
        R: 'static,
    {
        match self.0.entry(TypeId::of::<R>()) {
            Entry::Vacant(entry) => entry.insert(RefCell::new(Box::new(res))),
            Entry::Occupied(_) => panic!("Resource {} already present", type_name::<R>()),
        };
    }
}

impl Resources {
    /// Borrow a resource immutably
    ///
    /// # Panics
    ///
    /// Panics if the resource is not present.
    pub fn get<R>(&self) -> Res<'_, R>
    where
        R: 'static,
    {
        let ref_ = self
            .0
            .get(&TypeId::of::<R>())
            .unwrap_or_else(|| panic!("Resource {} not present", type_name::<R>()))
            .try_borrow()
            .unwrap_or_else(|_err| panic!("Resource {} already borrwed", type_name::<R>()));

        Res(Ref::map(ref_, |ref_| unsafe {
            &*(ref_.deref() as *const dyn Any as *const R)
        }))
    }

    /// Borrow a resource mutably
    ///
    /// # Panics
    ///
    /// Panics if the resource is not present.
    pub fn get_mut<R>(&self) -> ResMut<'_, R>
    where
        R: 'static,
    {
        let ref_ = self
            .0
            .get(&TypeId::of::<R>())
            .unwrap_or_else(|| panic!("Resource {} not present", type_name::<R>()))
            .try_borrow_mut()
            .unwrap_or_else(|_err| panic!("Resource {} already borrwed", type_name::<R>()));

        ResMut(RefMut::map(ref_, |ref_| unsafe {
            &mut *(ref_.deref_mut() as *mut dyn Any as *mut R)
        }))
    }
}

/// An immutable borrow of a resource.
pub struct Res<'a, R>(Ref<'a, R>);

impl<R> Deref for Res<'_, R> {
    type Target = R;

    fn deref(&self) -> &R {
        self.0.deref()
    }
}

/// A mutable borrow of a resource.
pub struct ResMut<'a, R>(RefMut<'a, R>);

impl<R> Deref for ResMut<'_, R> {
    type Target = R;

    fn deref(&self) -> &R {
        self.0.deref()
    }
}

impl<R> DerefMut for ResMut<'_, R> {
    fn deref_mut(&mut self) -> &mut R {
        self.0.deref_mut()
    }
}

#[derive(Default)]
struct TypeIdHasher(u64);

impl Hasher for TypeIdHasher {
    fn write_u64(&mut self, val: u64) {
        self.0 = val;
    }

    fn write(&mut self, _val: &[u8]) {
        unreachable!();
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_then_get() {
        let mut resources = Resources::new();

        resources.insert(42_u64);

        let res = resources.get::<u64>();
        assert_eq!(*res, 42);
    }

    #[test]
    fn get_mut_then_get() {
        let mut resources = Resources::new();

        resources.insert(42_u64);

        {
            let mut res = resources.get_mut::<u64>();
            *res = 23;
        }

        let res = resources.get::<u64>();
        assert_eq!(*res, 23);
    }

    #[test]
    #[should_panic]
    fn insert_does_not_replace() {
        let mut resources = Resources::new();

        resources.insert(23_i32);
        resources.insert(42_i32);
    }

    #[test]
    fn borrows_can_be_shared() {
        let mut resources = Resources::new();

        resources.insert(23_i32);

        let _res = resources.get::<i32>();
        let _res = resources.get::<i32>();
    }

    #[test]
    #[should_panic]
    fn mutable_borrows_are_exclusive() {
        let mut resources = Resources::new();

        resources.insert(23_i32);

        let _res = resources.get_mut::<i32>();
        let _res = resources.get_mut::<i32>();
    }
}
