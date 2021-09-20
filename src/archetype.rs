use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::any::{type_name, TypeId};
use std::cell::{Ref, RefCell, RefMut};
use std::cmp::Reverse;
use std::mem::align_of;
use std::ops::{Deref, DerefMut};
use std::ptr::copy_nonoverlapping;

pub struct Archetype {
    types: Box<[TypeMetadata]>,
    layout: Layout,
    len: u32,
    cap: u32,
    ptr: *mut u8,
}

impl Archetype {
    pub fn new(types: TypeMetadataSet) -> Self {
        assert!(types.0.len() <= u16::MAX as usize);

        let max_align = types
            .0
            .iter()
            .map(|ty| ty.layout.align())
            .max()
            .unwrap_or(1);

        let layout = Layout::from_size_align(0, max_align).unwrap();
        let ptr = max_align as *mut u8;

        Self {
            types: types.0.into(),
            layout,
            len: 0,
            cap: 0,
            ptr,
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
        if drop {
            for ty in &*self.types {
                let ptr = ty.base_pointer.add(ty.layout.size() * idx as usize);

                (ty.drop)(ptr);
            }
        }

        self.len -= 1;

        if idx != self.len {
            for ty in &*self.types {
                let size = ty.layout.size();

                let src_ptr = ty.base_pointer.add(size * self.len as usize);
                let dst_ptr = ty.base_pointer.add(size * idx as usize);

                copy_nonoverlapping(src_ptr, dst_ptr, size);
            }

            true
        } else {
            false
        }
    }

    pub fn clear(&mut self) {
        let len = self.len;
        self.len = 0;

        for ty in &*self.types {
            unsafe {
                for idx in 0..len {
                    let ptr = ty.base_pointer.add(ty.layout.size() * idx as usize);

                    (ty.drop)(ptr);
                }
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn grow(&mut self) {
        let new_cap = self.cap.checked_add(self.cap.max(8)).unwrap() as usize;

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

        let mut new_offsets = Vec::<usize>::with_capacity(types.0.len());
        let mut new_size = 0;

        for ty in types.0.iter() {
            new_offsets.push(new_size);

            new_size = new_size
                .checked_add(ty.layout.size().checked_mul(new_cap).unwrap())
                .unwrap();
        }

        let new_layout = Layout::from_size_align(new_size, self.layout.align()).unwrap();

        let new_ptr = if new_layout.size() != 0 {
            unsafe { alloc(new_layout) }
        } else {
            new_layout.align() as *mut u8
        };
        if new_ptr.is_null() {
            handle_alloc_error(new_layout);
        }

        unsafe {
            for (ty, new_offset) in types.0.iter_mut().zip(&new_offsets) {
                let new_base_pointer = new_ptr.add(*new_offset);

                copy_nonoverlapping(
                    ty.base_pointer,
                    new_base_pointer,
                    ty.layout.size() * self.cap as usize,
                );

                ty.base_pointer = new_base_pointer;
            }

            if self.layout.size() != 0 {
                dealloc(self.ptr, self.layout);
            }
        }

        self.layout = new_layout;
        self.ptr = new_ptr;

        self.cap = new_cap as u32;
    }
}

impl Drop for Archetype {
    fn drop(&mut self) {
        self.clear();

        unsafe {
            if self.layout.size() != 0 {
                dealloc(self.ptr, self.layout);
            }
        }
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

    pub fn find<C>(&self) -> Option<u16>
    where
        C: 'static,
    {
        self.types
            .binary_search_by_key(&TypeId::of::<C>(), |ty| ty.id)
            .map(|idx| idx as u16)
            .ok()
    }
}

impl Archetype {
    pub unsafe fn pointer<C>(&mut self, idx: u32) -> *mut C
    where
        C: 'static,
    {
        debug_assert!(idx < self.len);

        let ty = self.find::<C>().unwrap();
        let ptr = self.base_pointer::<C>(ty);

        ptr.add(idx as usize)
    }

    pub unsafe fn move_(src: &mut Self, dst: &mut Self, src_idx: u32, dst_idx: u32) {
        debug_assert!(src_idx < src.len);
        debug_assert!(dst_idx < dst.len);

        let mut dst_types = &*dst.types;

        for src_ty in &*src.types {
            let dst_ty = match dst_types.iter().position(|ty| ty.id == src_ty.id) {
                Some(dst_ty) => {
                    dst_types = &dst_types[dst_ty..];
                    &dst_types[0]
                }
                None => continue,
            };

            let size = src_ty.layout.size();

            let src_ptr = src_ty.base_pointer.add(size * src_idx as usize);
            let dst_ptr = dst_ty.base_pointer.add(size * dst_idx as usize);

            copy_nonoverlapping(src_ptr, dst_ptr, size);
        }
    }
}

impl Archetype {
    unsafe fn type_metadata<C>(&self, ty: u16) -> &TypeMetadata
    where
        C: 'static,
    {
        let ty = ty as usize;
        debug_assert!(ty < self.types.len());
        let ty = self.types.get_unchecked(ty);
        debug_assert_eq!(ty.id, TypeId::of::<C>());

        ty
    }

    pub unsafe fn borrow<C>(&self, ty: u16) -> Ref<'_, ()>
    where
        C: 'static,
    {
        self.type_metadata::<C>(ty)
            .borrow
            .try_borrow()
            .unwrap_or_else(|_err| panic!("Component {} already borrowed", type_name::<C>()))
    }

    pub unsafe fn borrow_mut<C>(&self, ty: u16) -> RefMut<'_, ()>
    where
        C: 'static,
    {
        self.type_metadata::<C>(ty)
            .borrow
            .try_borrow_mut()
            .unwrap_or_else(|_err| panic!("Component {} already borrowed", type_name::<C>()))
    }

    pub unsafe fn base_pointer<C>(&self, ty: u16) -> *mut C
    where
        C: 'static,
    {
        let ty = self.type_metadata::<C>(ty);

        ty.base_pointer.cast::<C>()
    }
}

impl Archetype {
    pub unsafe fn get<C>(&self, idx: u32) -> Option<Comp<'_, C>>
    where
        C: 'static,
    {
        debug_assert!(idx < self.len);

        let ty = self.find::<C>()?;
        let _ref = self.borrow::<C>(ty);
        let ptr = self.base_pointer::<C>(ty);

        let val = &*ptr.add(idx as usize);

        Some(Comp { _ref, val })
    }

    pub unsafe fn get_mut<C>(&self, idx: u32) -> Option<CompMut<'_, C>>
    where
        C: 'static,
    {
        debug_assert!(idx < self.len);

        let ty = self.find::<C>()?;
        let _ref = self.borrow_mut::<C>(ty);
        let ptr = self.base_pointer::<C>(ty);

        let val = &mut *ptr.add(idx as usize);

        Some(CompMut { _ref, val })
    }
}

/// An immutable borrow of a component.
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

/// A mutable borrow of a component.
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
    base_pointer: *mut u8,
    borrow: RefCell<()>,
}

impl Clone for TypeMetadata {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            layout: self.layout,
            drop: self.drop,
            base_pointer: self.layout.align() as *mut u8,
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
            base_pointer: align_of::<C>() as *mut u8,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reverse_sorting_by_alignment_avoids_padding() {
        let mut types = TypeMetadataSet::default();
        types.insert::<u64>();
        types.insert::<u32>();
        types.insert::<u16>();
        types.insert::<u8>();

        let mut archetype = Archetype::new(types);
        let _ent = unsafe { archetype.alloc() };

        assert_eq!(archetype.layout.size(), 8 * (8 + 4 + 2 + 1));
        assert_eq!(archetype.layout.align(), 8);

        assert_eq!(archetype.len, 1);
        assert_eq!(archetype.cap, 8);

        assert_eq!(archetype.types.len(), 4);

        unsafe {
            let ty = archetype.find::<u64>().unwrap();
            let base_pointer = archetype.base_pointer::<u64>(ty);
            assert_eq!(base_pointer, archetype.ptr.add(0).cast());

            let ty = archetype.find::<u32>().unwrap();
            let base_pointer = archetype.base_pointer::<u32>(ty);
            assert_eq!(base_pointer, archetype.ptr.add(8 * 8).cast());

            let ty = archetype.find::<u16>().unwrap();
            let base_pointer = archetype.base_pointer::<u16>(ty);
            assert_eq!(base_pointer, archetype.ptr.add(8 * (8 + 4)).cast());

            let ty = archetype.find::<u8>().unwrap();
            let base_pointer = archetype.base_pointer::<u8>(ty);
            assert_eq!(base_pointer, archetype.ptr.add(8 * (8 + 4 + 2)).cast());
        }
    }
}
