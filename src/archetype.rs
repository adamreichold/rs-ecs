use std::alloc::{alloc, dealloc, Layout};
use std::any::{type_name, TypeId};
use std::cell::{Ref, RefCell, RefMut, UnsafeCell};
use std::cmp::Reverse;
use std::ops::{Deref, DerefMut};
use std::ptr::{copy_nonoverlapping, NonNull};

pub struct Archetype {
    types: Box<[TypeMetadata]>,
    layout: Layout,
    len: u32,
    cap: u32,
    ptr: UnsafeCell<NonNull<u8>>,
}

impl Archetype {
    pub fn new(types: TypeMetadataSet) -> Self {
        let max_align = types
            .0
            .iter()
            .map(|ty| ty.layout.align())
            .max()
            .unwrap_or(1);

        let layout = Layout::from_size_align(0, max_align).unwrap();
        let ptr = NonNull::new(max_align as *mut u8).unwrap();

        Self {
            types: types.0.into(),
            layout,
            len: 0,
            cap: 0,
            ptr: UnsafeCell::new(ptr),
        }
    }
}

impl Archetype {
    pub fn len(&self) -> u32 {
        self.len
    }

    pub unsafe fn alloc(&mut self) -> u32 {
        if self.len == self.cap {
            self.grow();
        }

        let idx = self.len;
        self.len += 1;
        idx
    }

    #[must_use]
    pub unsafe fn free(&mut self, idx: u32, drop: bool) -> bool {
        let ptr = self.ptr.get_mut().as_ptr();

        if drop {
            for ty in &*self.types {
                let ptr = ptr.add(ty.offset + ty.layout.size() * idx as usize);

                (ty.drop)(ptr);
            }
        }

        self.len -= 1;

        if idx != self.len {
            for ty in &*self.types {
                let src_ptr = ptr.add(ty.offset + ty.layout.size() * self.len as usize);
                let dst_ptr = ptr.add(ty.offset + ty.layout.size() * idx as usize);

                copy_nonoverlapping(src_ptr, dst_ptr, ty.layout.size());
            }

            true
        } else {
            false
        }
    }

    #[cold]
    fn grow(&mut self) {
        let new_cap = self.cap.checked_add(self.len.max(8)).unwrap() as usize;

        let old_offsets = self.types.iter().map(|ty| ty.offset).collect::<Vec<_>>();

        struct SortOnDrop<'a>(&'a mut [TypeMetadata]);

        impl Drop for SortOnDrop<'_> {
            fn drop(&mut self) {
                self.0.sort_unstable_by_key(|ty| ty.id);
            }
        }

        let types = SortOnDrop(&mut self.types);

        types
            .0
            .sort_unstable_by_key(|ty| Reverse(ty.layout.align()));

        let mut max_align = 1;
        let mut sum_size = 0;
        for ty in types.0.iter_mut() {
            let align = ty.layout.align();
            let size = aligned(ty.layout.size(), align);
            let len = size.checked_mul(new_cap).unwrap();

            max_align = max_align.max(align);

            ty.offset = aligned(sum_size, align);
            sum_size = ty.offset.checked_add(len).unwrap();
        }

        drop(types);

        let new_layout = Layout::from_size_align(sum_size, max_align).unwrap();
        let new_ptr;

        unsafe {
            new_ptr = if sum_size != 0 {
                alloc(new_layout)
            } else {
                max_align as *mut u8
            };

            if self.layout.size() != 0 {
                let old_ptr = self.ptr.get_mut().as_ptr();

                for (ty, old_offset) in self.types.iter().zip(old_offsets) {
                    copy_nonoverlapping(
                        old_ptr.add(old_offset),
                        new_ptr.add(ty.offset),
                        ty.layout.size() * self.len as usize,
                    );
                }

                dealloc(self.ptr.get_mut().as_ptr(), self.layout);
            }
        }

        self.layout = new_layout;
        *self.ptr.get_mut() = NonNull::new(new_ptr).unwrap();

        self.cap = new_cap as u32;
    }
}

impl Archetype {
    pub fn types(&self) -> TypeMetadataSet {
        TypeMetadataSet(self.types.to_vec())
    }

    pub fn match_(&self, types: &TypeMetadataSet) -> bool {
        let lhs = self.types.iter().map(|ty| ty.id);
        let rhs = types.0.iter().map(|ty| ty.id);

        lhs.eq(rhs)
    }

    pub fn find<C>(&self) -> Option<usize>
    where
        C: 'static,
    {
        self.types
            .binary_search_by_key(&TypeId::of::<C>(), |ty| ty.id)
            .ok()
    }
}

impl Archetype {
    pub unsafe fn access<C>(&mut self, idx: u32) -> *mut C
    where
        C: 'static,
    {
        debug_assert!(idx < self.len);

        let ty = self.find::<C>().unwrap();
        let ty = &self.types[ty];

        let ptr = self.ptr.get_mut().as_ptr();
        let ptr = ptr.add(ty.offset + ty.layout.size() * idx as usize);

        ptr.cast::<C>()
    }

    pub unsafe fn move_(src: &mut Self, dst: &mut Self, src_idx: u32, dst_idx: u32) {
        debug_assert!(src_idx < src.len);
        debug_assert!(dst_idx < dst.len);

        let mut dst_types = &*dst.types;

        let src_ptr = src.ptr.get_mut().as_ptr();
        let dst_ptr = dst.ptr.get_mut().as_ptr();

        for src_ty in &*src.types {
            let dst_ty = match dst_types.iter().position(|ty| ty.id == src_ty.id) {
                Some(dst_ty) => {
                    dst_types = &dst_types[dst_ty..];
                    &dst_types[0]
                }
                None => continue,
            };

            let size = src_ty.layout.size();

            let src_ptr = src_ptr.add(src_ty.offset + size * src_idx as usize);
            let dst_ptr = dst_ptr.add(dst_ty.offset + size * dst_idx as usize);

            copy_nonoverlapping(src_ptr, dst_ptr, size);
        }
    }
}

impl Archetype {
    pub unsafe fn borrow<C>(&self, ty: usize) -> (Ref<'_, ()>, *const C)
    where
        C: 'static,
    {
        debug_assert!(ty < self.types.len());
        let ty = self.types.get_unchecked(ty);
        debug_assert_eq!(ty.id, TypeId::of::<C>());

        let ref_ = ty.borrow.borrow();
        let ptr = (*self.ptr.get()).as_ptr().add(ty.offset).cast::<C>();

        (ref_, ptr)
    }

    pub unsafe fn borrow_mut<C>(&self, ty: usize) -> (RefMut<'_, ()>, *mut C)
    where
        C: 'static,
    {
        debug_assert!(ty < self.types.len());
        let ty = self.types.get_unchecked(ty);
        debug_assert_eq!(ty.id, TypeId::of::<C>());

        let ref_ = ty.borrow.borrow_mut();
        let ptr = (*self.ptr.get()).as_ptr().add(ty.offset).cast::<C>();

        (ref_, ptr)
    }
}

impl Archetype {
    pub unsafe fn get<C>(&self, idx: u32) -> Option<Comp<'_, C>>
    where
        C: 'static,
    {
        debug_assert!(idx < self.len);

        let ty = self.find::<C>()?;
        let (_ref, ptr) = self.borrow::<C>(ty);

        let val = &*ptr.add(idx as usize);

        Some(Comp { _ref, val })
    }

    pub unsafe fn get_mut<C>(&self, idx: u32) -> Option<CompMut<'_, C>>
    where
        C: 'static,
    {
        debug_assert!(idx < self.len);

        let ty = self.find::<C>()?;
        let (_ref, ptr) = self.borrow_mut::<C>(ty);

        let val = &mut *ptr.add(idx as usize);

        Some(CompMut { _ref, val })
    }
}

impl Drop for Archetype {
    fn drop(&mut self) {
        if self.layout.size() != 0 {
            let ptr = self.ptr.get_mut().as_ptr();

            unsafe {
                for ty in &*self.types {
                    let ptr = ptr.add(ty.offset);

                    for idx in 0..self.len {
                        let ptr = ptr.add(ty.layout.size() * idx as usize);

                        (ty.drop)(ptr);
                    }
                }

                dealloc(ptr, self.layout);
            }
        }
    }
}

pub struct Comp<'a, C> {
    _ref: Ref<'a, ()>,
    val: &'a C,
}

impl<C> Deref for Comp<'_, C> {
    type Target = C;

    fn deref(&self) -> &C {
        self.val
    }
}

pub struct CompMut<'a, C> {
    _ref: RefMut<'a, ()>,
    val: &'a mut C,
}

impl<C> Deref for CompMut<'_, C> {
    type Target = C;

    fn deref(&self) -> &C {
        self.val
    }
}

impl<C> DerefMut for CompMut<'_, C> {
    fn deref_mut(&mut self) -> &mut C {
        self.val
    }
}

struct TypeMetadata {
    id: TypeId,
    layout: Layout,
    drop: unsafe fn(*mut u8),
    offset: usize,
    borrow: RefCell<()>,
}

impl Clone for TypeMetadata {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            layout: self.layout,
            drop: self.drop,
            offset: 0,
            borrow: Default::default(),
        }
    }
}

impl TypeMetadata {
    fn new<C>() -> Self
    where
        C: 'static,
    {
        unsafe fn drop_in_place<C>(ptr: *mut u8) {
            ptr.cast::<C>().drop_in_place()
        }

        Self {
            id: TypeId::of::<C>(),
            layout: Layout::new::<C>(),
            drop: drop_in_place::<C>,
            offset: 0,
            borrow: Default::default(),
        }
    }
}

#[derive(Default)]
pub struct TypeMetadataSet(Vec<TypeMetadata>);

impl TypeMetadataSet {
    pub fn insert<C>(&mut self)
    where
        C: 'static,
    {
        let ty = self.0.binary_search_by_key(&TypeId::of::<C>(), |ty| ty.id);

        match ty {
            Err(ty) => self.0.insert(ty, TypeMetadata::new::<C>()),
            Ok(_) => panic!("Component {} already present", type_name::<C>()),
        }
    }

    #[must_use]
    pub fn remove<C>(&mut self) -> Option<()>
    where
        C: 'static,
    {
        let ty = self
            .0
            .binary_search_by_key(&TypeId::of::<C>(), |ty| ty.id)
            .ok()?;

        self.0.remove(ty);

        Some(())
    }
}

fn aligned(val: usize, align: usize) -> usize {
    let rest = val % align;
    if rest != 0 {
        val.checked_add(align - rest).unwrap()
    } else {
        val
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aligned_aligns() {
        assert_eq!(aligned(0, 8), 0);
        assert_eq!(aligned(1, 8), 8);
        assert_eq!(aligned(7, 8), 8);
        assert_eq!(aligned(8, 8), 8);
        assert_eq!(aligned(9, 8), 16);
        assert_eq!(aligned(0, 1), 0);
        assert_eq!(aligned(1, 1), 1);
        assert_eq!(aligned(2, 1), 2);
    }
}
