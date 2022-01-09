use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::any::TypeId;
use std::cmp::Reverse;
use std::mem::{align_of, needs_drop};
use std::ptr::{copy_nonoverlapping, drop_in_place};
use std::slice::from_raw_parts_mut;

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
    pub unsafe fn free<const DROP: bool>(&mut self, idx: u32) -> bool {
        if DROP {
            for ty in &*self.types {
                let ptr = ty.base_pointer.add(ty.layout.size() * idx as usize);

                (ty.drop)(ptr, 1);
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
                (ty.drop)(ty.base_pointer, len as usize);
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

    pub unsafe fn base_pointer<C>(&self, ty: u16) -> *mut C
    where
        C: 'static,
    {
        let ty = self.type_metadata::<C>(ty);

        ty.base_pointer.cast::<C>()
    }

    pub unsafe fn pointer<C>(&self, ty: u16, idx: u32) -> *mut C
    where
        C: 'static,
    {
        debug_assert!(idx < self.len);

        let ptr = self.base_pointer::<C>(ty);

        ptr.add(idx as usize)
    }
}

impl Archetype {
    pub unsafe fn get<C>(&self, idx: u32) -> *mut C
    where
        C: 'static,
    {
        let ty = self.find::<C>().unwrap();
        self.pointer::<C>(ty, idx)
    }

    pub unsafe fn drop<C>(&mut self, idx: u32)
    where
        C: 'static,
    {
        if needs_drop::<C>() {
            if let Some(ty) = self.find::<C>() {
                let ty = self.types.get_unchecked(ty as usize);

                let ptr = ty.base_pointer.add(ty.layout.size() * idx as usize);

                (ty.drop)(ptr, 1);
            }
        }
    }
}

#[derive(Clone, Copy)]
struct TypeMetadata {
    id: TypeId,
    layout: Layout,
    drop: unsafe fn(*mut u8, usize),
    base_pointer: *mut u8,
}

impl TypeMetadata {
    fn new<C>() -> Self
    where
        C: 'static,
    {
        unsafe fn drop<C>(ptr: *mut u8, len: usize) {
            drop_in_place(from_raw_parts_mut(ptr.cast::<C>(), len))
        }

        Self {
            id: TypeId::of::<C>(),
            layout: Layout::new::<C>(),
            drop: drop::<C>,
            base_pointer: align_of::<C>() as *mut u8,
        }
    }
}

#[derive(Default)]
pub struct TypeMetadataSet(Vec<TypeMetadata>);

impl TypeMetadataSet {
    pub fn ids(&self) -> impl ExactSizeIterator<Item = TypeId> + '_ {
        self.0.iter().map(|ty| ty.id)
    }

    pub fn insert<C>(&mut self)
    where
        C: 'static,
    {
        if let Err(ty) = self.0.binary_search_by_key(&TypeId::of::<C>(), |ty| ty.id) {
            self.0.insert(ty, TypeMetadata::new::<C>());
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

    use std::cell::Cell;
    use std::rc::Rc;

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

    #[test]
    fn drops_all_component_values() {
        struct CountDrops(Rc<Cell<usize>>);

        impl Drop for CountDrops {
            fn drop(&mut self) {
                let drops = &self.0;

                drops.set(drops.get() + 1);
            }
        }

        let drops = Rc::new(Cell::new(0));

        let mut types = TypeMetadataSet::default();
        types.insert::<CountDrops>();

        let mut archetype = Archetype::new(types);

        unsafe {
            for _ in 0..32 {
                let ent = archetype.alloc();

                archetype
                    .get::<CountDrops>(ent)
                    .write(CountDrops(drops.clone()));
            }
        }

        drop(archetype);

        assert_eq!(drops.get(), 32);
    }
}
