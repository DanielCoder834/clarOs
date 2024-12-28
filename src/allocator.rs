use alloc::alloc::{GlobalAlloc, Layout};
use core::ptr::null_mut;

use x86_64::structures::paging::{FrameAllocator, Mapper, Page, PageTableFlags, Size4KiB};
use x86_64::structures::paging::mapper::MapToError;
use x86_64::VirtAddr;

use crate::allocator::fixed_size_block::FixedSizeBlockAllocator;

#[global_allocator]
static ALLOCATOR: Locked<FixedSizeBlockAllocator> = Locked::new(FixedSizeBlockAllocator::new());

pub struct Dummy;

unsafe impl GlobalAlloc for Dummy {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        null_mut()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        panic!("dealloc should be never called")
    }
}

pub const HEAP_START: usize = 0x_4444_4444_0000;
pub const HEAP_SIZE: usize = 100 * 1024;

pub fn init_heap(
    mapper: &mut impl Mapper<Size4KiB>,
    frame_allocator: &mut impl FrameAllocator<Size4KiB>,
) -> Result<(), MapToError<Size4KiB>> {
    let page_range = {
        let heap_start = VirtAddr::new(HEAP_START as u64);
        let heap_end = heap_start + HEAP_SIZE - 1u64;
        let heap_start_page = Page::containing_address(heap_start);
        let heap_end_page = Page::containing_address(heap_end);
        Page::range_inclusive(heap_start_page, heap_end_page)
    };

    for page in page_range {
        let frame = frame_allocator
            .allocate_frame()
            .ok_or(MapToError::FrameAllocationFailed)?;
        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;
        unsafe {
            mapper.map_to(page, frame, flags, frame_allocator)?.flush()
        };
    }

    unsafe {
        ALLOCATOR.lock().init(HEAP_START, HEAP_SIZE);
    }

    Ok(())
}

pub struct Locked<A> {
    inner: spin::Mutex<A>,
}

impl <A> Locked<A> {
    pub const fn new(inner: A) -> Self {
        Locked {
            inner: spin::Mutex::new(inner),
        }
    }

    pub fn lock(&self) -> spin::MutexGuard<A> {
        self.inner.lock()
    }
}

fn align_up(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

pub mod bump {
    use core::alloc::{GlobalAlloc, Layout};
    use core::ptr;

    use crate::allocator::Locked;

    use super::align_up;

    pub struct BumpAllocator {
        heap_start: usize,
        heap_end: usize,
        next: usize,
        allocations: usize,
    }

    impl BumpAllocator {
        pub const fn new() -> Self {
            BumpAllocator {
                heap_start: 0,
                heap_end: 0,
                next: 0,
                allocations: 0,
            }
        }

        pub unsafe fn init(&mut self, heap_start: usize, heap_size: usize) {
            self.heap_start = heap_start;
            self.heap_end = heap_start + heap_size;
            self.next = heap_start;
        }
    }

    unsafe impl GlobalAlloc for Locked<BumpAllocator> {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let mut bump = self.lock();
            let alloc_start = align_up(bump.next, layout.align());
            let alloc_end = match alloc_start.checked_add(layout.size()) {
                Some(end) => end,
                None => return ptr::null_mut(),
            };
            if alloc_end > bump.heap_end {
                ptr::null_mut()
            } else {
                bump.next = alloc_end;
                bump.allocations += 1;
                alloc_start as *mut u8
            }
        }

        unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
            let mut bump = self.lock();
            bump.allocations -= 1;
            if bump.allocations == 0 {
                bump.next = bump.heap_start;
            }
        }
    }
}

pub mod linked_list {
    use core::{mem, ptr};
    use core::alloc::{GlobalAlloc, Layout};

    use super::{align_up, Locked};

    struct ListNode {
        size: usize,
        next: Option<&'static mut ListNode>,
    }

    impl ListNode {
        const fn new(size: usize) -> Self {
            ListNode {size, next: None}
        }

        fn start_addr(&self) -> usize {
            self as *const Self as usize
        }

        fn end_addr(&self) -> usize {
            self.start_addr() + self.size
        }
    }

    pub struct LinkedListAllocator {
        head: ListNode,
    }

    impl LinkedListAllocator {
        pub const fn new() -> Self {
            Self {
                head: ListNode::new(0),
            }
        }

        pub unsafe fn init(&mut self, heap_start: usize, heap_size: usize) {
            self.add_free_region(heap_start, heap_size);
        }

        unsafe fn add_free_region(&mut self, addr: usize, size: usize) {
            assert_eq!(align_up(addr, mem::align_of::<ListNode>()), addr);
            assert!(size >= mem::size_of::<ListNode>());

            let mut node = ListNode::new(size);
            node.next = self.head.next.take();
            let node_ptr = addr as *mut ListNode;
            node_ptr.write(node);
            self.head.next = Some(&mut *node_ptr)
        }

        fn find_region(&mut self, size: usize, align: usize) -> Option<(&'static mut ListNode, usize)> {
            let mut current = &mut self.head;
            while let Some(ref mut region) = current.next {
                if let Ok(alloc_start) = Self::alloc_from_region(&region, size, align) {
                    let next = region.next.take();
                    let ret = Some((current.next.take().unwrap(), alloc_start));
                    current.next = next;
                    return ret;
                } else {
                    current = current.next.as_mut().unwrap();
                }
            }
            None
        }

        fn alloc_from_region(region: &ListNode, size: usize, align: usize) -> Result<usize, ()> {
            let alloc_start = align_up(region.start_addr(), align);
            let alloc_end = alloc_start.checked_add(size).ok_or(())?;

            if alloc_end > region.end_addr() {
                return Err(());
            }

            let excess_size = region.end_addr() - alloc_end;
            if excess_size > 0 && excess_size < mem::size_of::<ListNode>() {
                return Err(());
            }

            Ok(alloc_start)
        }
        fn size_align(layout: Layout) -> (usize, usize) {
            let layout = layout
                .align_to(mem::align_of::<ListNode>())
                .expect("adjusting alignment failed")
                .pad_to_align();
            let size = layout.size().max(mem::size_of::<ListNode>());
            (size, layout.align())
        }
    }

    unsafe impl GlobalAlloc for Locked<LinkedListAllocator> {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let (size, align) = LinkedListAllocator::size_align(layout);
            let mut allocator = self.lock();

            if let Some((region, alloc_start)) = allocator.find_region(size, align) {
                let alloc_end = alloc_start.checked_add(size).expect("overflow");
                let excess_size = region.end_addr() - alloc_end;
                if excess_size > 0 {
                    allocator.add_free_region(alloc_end, excess_size);
                }
                alloc_start as *mut u8
            } else {
                ptr::null_mut()
            }
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            // let alloc = self.lock();
            let (size, _) = LinkedListAllocator::size_align(layout);

            self.lock().add_free_region(ptr as usize, size)
        }
    }
}

pub mod fixed_size_block {
    use core::alloc::{GlobalAlloc, Layout};
    use core::ptr;
    use core::ptr::NonNull;

    use crate::allocator::Locked;

    const BLOCK_SIZES: &[usize] = &[8,16,32, 64, 128, 256, 512, 1024, 2048];
    struct ListNode {
        next: Option<&'static mut ListNode>,
    }

    pub struct FixedSizeBlockAllocator {
        list_heads: [Option<&'static mut ListNode>; BLOCK_SIZES.len()],
        fallback_allocator: linked_list_allocator::Heap,
    }

    impl FixedSizeBlockAllocator {
        pub const fn new() -> Self {
            const EMPTY: Option<&'static mut ListNode> = None;
            FixedSizeBlockAllocator {
                list_heads: [EMPTY; BLOCK_SIZES.len()],
                fallback_allocator: linked_list_allocator::Heap::empty(),
            }
        }

        pub unsafe fn init(&mut self, heap_start: usize, heap_size: usize) {
            self.fallback_allocator.init(heap_start, heap_size);
        }

        fn fallback_alloc(&mut self, layout: Layout) -> *mut u8 {
            match self.fallback_allocator.allocate_first_fit(layout) {
                Ok(ptr) => ptr.as_ptr(),
                Err(_) => ptr::null_mut(),
            }
        }
    }

    fn list_index(layout: &Layout) -> Option<usize> {
        let required_block_size = layout.size().max(layout.align());
        BLOCK_SIZES.iter().position(|&s| s >= required_block_size)
    }

    unsafe impl GlobalAlloc for Locked<FixedSizeBlockAllocator> {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let mut allocator = self.lock();
            match list_index(&layout) {
                Some(index) => {
                    match allocator.list_heads[index].take() {
                        Some(node) => {
                            allocator.list_heads[index] = node.next.take();
                            node as *mut ListNode as *mut u8
                        }
                        None => {
                            let block_size = BLOCK_SIZES[index];
                            let block_align = block_size;
                            let layout = Layout::from_size_align(block_size, block_align)
                                .unwrap();
                            allocator.fallback_alloc(layout)
                        }
                    }
                }
                None => allocator.fallback_alloc(layout),
            }
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            let mut allocator = self.lock();
            match list_index(&layout) {
                Some(index) => {
                    let new_node = ListNode {
                        next: allocator.list_heads[index].take(),
                    };

                    assert!(size_of::<ListNode>() <= BLOCK_SIZES[index]);
                    assert!(align_of::<ListNode>() <= BLOCK_SIZES[index]);

                    let new_node_ptr = ptr as *mut ListNode;
                    new_node_ptr.write(new_node);
                    allocator.list_heads[index] = Some(&mut *new_node_ptr);
                }
                None => {
                    let ptr = NonNull::new(ptr).unwrap();
                    allocator.fallback_allocator.deallocate(ptr, layout);
                }
            }
        }
    }
}

