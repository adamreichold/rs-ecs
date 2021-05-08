use std::any::{type_name, Any, TypeId};
use std::cell::{Ref, RefCell, RefMut};
use std::collections::hash_map::{Entry, HashMap};
use std::hash::{BuildHasherDefault, Hasher};
use std::ops::{Deref, DerefMut};

#[derive(Default)]
pub struct Resources(HashMap<TypeId, RefCell<Box<dyn Any>>, BuildHasherDefault<TypeIdHasher>>);

impl Resources {
    pub fn new() -> Self {
        Default::default()
    }
}

impl Resources {
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
    pub fn get<R>(&self) -> Res<'_, R>
    where
        R: 'static,
    {
        let ref_ = self.0[&TypeId::of::<R>()].borrow();

        Res(Ref::map(ref_, |ref_| unsafe {
            &*(ref_.deref() as *const dyn Any as *const R)
        }))
    }

    pub fn get_mut<R>(&self) -> ResMut<'_, R>
    where
        R: 'static,
    {
        let ref_ = self.0[&TypeId::of::<R>()].borrow_mut();

        ResMut(RefMut::map(ref_, |ref_| unsafe {
            &mut *(ref_.deref_mut() as *mut dyn Any as *mut R)
        }))
    }

    pub fn mut_get_mut<R>(&mut self) -> &mut R
    where
        R: 'static,
    {
        let res = self.0.get_mut(&TypeId::of::<R>()).unwrap().get_mut();

        unsafe { &mut *(res.deref_mut() as *mut dyn Any as *mut R) }
    }
}

pub struct Res<'a, R>(Ref<'a, R>);

impl<R> Deref for Res<'_, R> {
    type Target = R;

    fn deref(&self) -> &R {
        self.0.deref()
    }
}

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
    fn mut_get_mut_then_get() {
        let mut resources = Resources::new();

        resources.insert(42_u64);

        {
            let res = resources.mut_get_mut::<u64>();
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
