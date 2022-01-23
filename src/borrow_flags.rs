use std::any::{type_name, TypeId};
use std::cell::UnsafeCell;

use crate::archetype::TypeMetadataSet;

#[derive(Default)]
pub struct BorrowFlags(Vec<(TypeId, UnsafeCell<isize>)>);

impl BorrowFlags {
    pub fn insert(&mut self, types: &TypeMetadataSet) {
        for id in types.ids() {
            if let Err(idx) = self.0.binary_search_by_key(&id, |(id, _)| *id) {
                assert!(self.0.len() < u16::MAX as usize);

                self.0.insert(idx, (id, UnsafeCell::new(0)));
            }
        }
    }

    pub fn find<C>(&self) -> Option<u16>
    where
        C: 'static,
    {
        self.find_impl(&TypeId::of::<C>())
    }

    fn find_impl(&self, key: &TypeId) -> Option<u16> {
        self.0
            .binary_search_by_key(key, |(id, _)| *id)
            .map(|idx| idx as u16)
            .ok()
    }

    #[cfg(debug_assertions)]
    fn flag<C>(&self, ty: u16) -> &UnsafeCell<isize>
    where
        C: 'static,
    {
        let (id, flag) = &self.0[ty as usize];
        assert_eq!(id, &TypeId::of::<C>());
        flag
    }

    #[cfg(not(debug_assertions))]
    unsafe fn flag_unchecked(&self, ty: u16) -> &UnsafeCell<isize> {
        &self.0.get_unchecked(ty as usize).1
    }

    pub unsafe fn borrow<C>(&self, ty: u16) -> Ref<'_>
    where
        C: 'static,
    {
        #[cfg(debug_assertions)]
        let flag = self.flag::<C>(ty);
        #[cfg(not(debug_assertions))]
        let flag = self.flag_unchecked(ty);

        Ref::new(flag).unwrap_or_else(|| panic!("Component {} already borrowed", type_name::<C>()))
    }

    pub unsafe fn borrow_mut<C>(&self, ty: u16) -> RefMut<'_>
    where
        C: 'static,
    {
        #[cfg(debug_assertions)]
        let flag = self.flag::<C>(ty);
        #[cfg(not(debug_assertions))]
        let flag = self.flag_unchecked(ty);

        RefMut::new(flag)
            .unwrap_or_else(|| panic!("Component {} already borrowed", type_name::<C>()))
    }
}

pub struct Ref<'a>(&'a UnsafeCell<isize>);

impl<'a> Ref<'a> {
    pub(crate) fn new(borrow: &'a UnsafeCell<isize>) -> Option<Self> {
        let readers = unsafe { &mut *borrow.get() };

        let new_readers = readers.wrapping_add(1);

        if new_readers <= 0 {
            cold();
            return None;
        }

        *readers = new_readers;

        Some(Self(borrow))
    }
}

impl Drop for Ref<'_> {
    fn drop(&mut self) {
        unsafe {
            *self.0.get() -= 1;
        }
    }
}

pub struct RefMut<'a>(&'a UnsafeCell<isize>);

impl<'a> RefMut<'a> {
    pub(crate) fn new(borrow: &'a UnsafeCell<isize>) -> Option<Self> {
        let writers = unsafe { &mut *borrow.get() };

        if *writers != 0 {
            cold();
            return None;
        }

        *writers = -1;

        Some(Self(borrow))
    }
}

impl Drop for RefMut<'_> {
    fn drop(&mut self) {
        unsafe {
            *self.0.get() = 0;
        }
    }
}

#[cold]
#[inline(always)]
fn cold() {}
