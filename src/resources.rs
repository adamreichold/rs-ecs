use std::any::{Any, TypeId};
use std::cell::{Ref, RefCell, RefMut};
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

#[derive(Default)]
pub struct Resources(HashMap<TypeId, RefCell<Box<dyn Any>>>);

impl Resources {
    pub fn insert<R>(&mut self, res: R)
    where
        R: 'static,
    {
        self.0
            .insert(TypeId::of::<R>(), RefCell::new(Box::new(res)));
    }
}

impl Resources {
    pub fn get<R>(&self) -> Res<'_, R>
    where
        R: 'static,
    {
        let ref_ = self.0[&TypeId::of::<R>()].borrow();

        Res(Ref::map(ref_, |ref_| ref_.downcast_ref().unwrap()))
    }

    pub fn get_mut<R>(&self) -> ResMut<'_, R>
    where
        R: 'static,
    {
        let ref_ = self.0[&TypeId::of::<R>()].borrow_mut();

        ResMut(RefMut::map(ref_, |ref_| ref_.downcast_mut().unwrap()))
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

#[test]
fn it_works() {
    let mut resources = Resources::default();

    resources.insert(23_i32);
    resources.insert(42_u64);

    {
        let val = resources.get::<u64>();
        assert_eq!(*val, 42);

        let mut val = resources.get_mut::<i32>();
        *val *= -1;
    }

    {
        let val = resources.get::<i32>();
        assert_eq!(*val, -23);
    }
}
