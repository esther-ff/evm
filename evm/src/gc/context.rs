use core::alloc::Layout;
use core::cell::Cell;
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::{self, NonNull};
use std::alloc::dealloc;

use super::gc::Gc;
use super::traits::{ToHeap, Trace};

#[repr(transparent)]
pub(crate) struct MutPeriod<'gc> {
    cx: Cx,
    _lifetime: PhantomData<Cell<&'gc ()>>,
}

impl<'gc> MutPeriod<'gc> {
    pub fn allocate<T: ToHeap<'gc>>(&self, data: T) -> NonNull<TypedGcBox<T>> {
        self.cx.alloc(data)
    }

    pub fn barrier(&self, parent: GcBox) {
        self.cx.barrier(parent);
    }

    pub fn metrics(&self) -> &GcMetrics {
        self.cx.metrics()
    }
}

// every unit is in bytes
// if it refers to memory
#[derive(Debug)]
pub struct GcMetrics {
    pub allocated: Cell<usize>,

    pub freed: Cell<usize>,
}

impl GcMetrics {
    pub fn new() -> Self {
        Self {
            allocated: Cell::new(0),
            freed: Cell::new(0),
        }
    }

    pub fn allocated(&self, add: usize) {
        self.allocated.update(|x| x + add);
    }

    pub fn freed(&self, add: usize) {
        self.freed.update(|x| x + add);
    }
}

#[derive(Clone, Copy)]
enum GcState {
    DoingNothing,
    Marking,
    Sweeping,
}

pub struct Cx {
    /// the linked list of allocated objects (it's head)
    list_of_objects: Cell<Option<GcBox>>,

    /// metrics
    metrics: GcMetrics,

    /// pointer from which we should start to sweep objects
    sweep_head: Cell<Option<GcBox>>,

    /// previous sweeped object
    /// used to keep track if we need
    /// to adjust the `all_allocated` list
    prev_sweep: Option<GcBox>,

    /// what is the gc doing currently
    state: GcState,

    /// do we need to trace the root object
    need_to_trace_root: bool,

    /// "gray" objects
    /// that need to be traced
    gray_objects: Queue<GcBox>,

    /// gray objects that became gray
    /// again due to triggering a barrier
    again_gray: Queue<GcBox>,
}

impl core::ops::Drop for Cx {
    fn drop(&mut self) {
        let mut cursor = self.list_of_objects.get();

        while let Some(gcbox) = cursor {
            let header = gcbox.header();
            cursor = header.next.get();
            if header.live.get() {
                unsafe {
                    gcbox.drop_in_place();
                }
            }

            unsafe {
                gcbox.deallocate();
            }
        }
    }
}

impl Cx {
    pub fn new() -> Self {
        Self {
            list_of_objects: Cell::new(None),
            metrics: GcMetrics::new(),
            state: GcState::DoingNothing,
            sweep_head: Cell::new(None),
            prev_sweep: None,
            need_to_trace_root: true,
            gray_objects: Queue::new(),
            again_gray: Queue::new(),
        }
    }

    pub fn to_mut_period<'gc>(&self) -> &MutPeriod<'gc> {
        // unsafe { transmute::<&Self, &MutPeriod>(self) }
        unsafe { &*(ptr::from_ref(self).cast::<MutPeriod>()) }
    }

    pub fn alloc<'gc, T: ToHeap<'gc>>(&self, victim: T) -> NonNull<TypedGcBox<T>> {
        let header = Header::new::<T>();

        header.next.set(self.list_of_objects.get());
        header.set_needs_trace(T::NEEDS_TO_BE_TRACED);
        header.set_live(true);

        let size_alloc = header.box_size();
        self.metrics.allocated(size_alloc);

        let mut boxxy = Box::new(MaybeUninit::<TypedGcBox<T>>::uninit());

        // rewrite later to use a bump allocator
        unsafe {
            ptr::write(boxxy.as_mut_ptr(), TypedGcBox::new(header, victim));

            let ptr = NonNull::new_unchecked(Box::into_raw(boxxy).cast::<TypedGcBox<T>>());
            self.list_of_objects.set(Some(GcBox::erase_type(ptr)));
            ptr
        }
    }

    fn metrics(&self) -> &GcMetrics {
        &self.metrics
    }

    pub fn mark_root_for_tracing(&mut self) {
        // before marking we know to trace the root
        // after sweeping we also know to do that
        // therefore it is only sensical
        // to mark it for tracing during `GcState::Marking`
        if let GcState::Marking = self.state {
            self.need_to_trace_root = true;
        }
    }

    fn put_to_gray_again_queue(&self, black: GcBox) {
        debug_assert_eq!(
            black.header().color.get(),
            GcColor::Black,
            "color given to this function was invalid"
        );

        black.header().change_color(GcColor::Gray);
        self.again_gray.push(black);
    }

    pub fn gc_cycle<'gc, R>(&mut self, root: &R)
    where
        R: ToHeap<'gc> + ?Sized,
    {
        loop {
            match self.state {
                GcState::DoingNothing => self.state = GcState::Marking,

                GcState::Marking => {
                    if self.mark_alloc(root) {
                        self.state = GcState::Sweeping;

                        self.sweep_head.set(self.list_of_objects.get());
                    }
                }

                GcState::Sweeping => {
                    if self.sweep_alloc() {
                        self.need_to_trace_root = true;

                        self.state = GcState::DoingNothing;

                        break;
                    }
                }
            }
        }
    }

    // returns a boolean
    // if it's true, break out of the cycle
    // if it's false, continue
    fn mark_alloc<'gc, R>(&mut self, root: &R) -> bool
    where
        R: ToHeap<'gc> + ?Sized,
    {
        let gray = if let Some(gray) = self.gray_objects.pop() {
            Some(gray)
        } else {
            self.again_gray.pop()
        };

        if let Some(object) = gray {
            object.header().change_color(GcColor::Black); // mark the gray ones as black;
            object.trace_self(self);

            false
        } else if self.need_to_trace_root {
            // we need to trace through the entire root
            root.trace(self);
            self.need_to_trace_root = false;
            false
        } else {
            // nothing to be done
            true
        }
    }

    // returns a boolean
    // if it's true, break out of the cycle
    // if it's false, continue
    fn sweep_alloc(&mut self) -> bool {
        // sweep_head is set by `mark_alloc` after the end of a
        // marking cycle, therefore if it's none then we have
        // nothing to sweep.
        let Some(victim) = self.sweep_head.get() else {
            self.prev_sweep = None;
            return true;
        };

        let header = victim.header();
        let size = header.box_size();
        let next = header.next.get();

        self.sweep_head.set(next);

        // dbg!(next);

        match header.color.get() {
            // all gray objects must have been converted to a different color
            GcColor::Gray => {
                unreachable!("impossible for a gray object to be observed by this function")
            }

            GcColor::Black => {
                // prev_sweep represents the previous box of an iterator
                // by setting this one as previous
                // if another iteration hits a white-colored box
                // it can "stitch" this box and the box after the white one
                // while removing the white one from the list
                self.prev_sweep = Some(victim);
                header.color.set(GcColor::White);
            }

            GcColor::White => {
                if let Some(prev) = self.prev_sweep {
                    // this does the "stitching"
                    // mentioned above
                    prev.header().next.set(next);
                } else {
                    self.list_of_objects.set(next);
                }

                if header.live.get() {
                    unsafe {
                        victim.drop_in_place();
                    }

                    header.set_live(false);

                    self.metrics.freed(size);
                }

                // as the object is marked currently as white
                // it has no pointer tracing to it
                // so it can be safely deallocated
                unsafe {
                    victim.deallocate();
                }
            }
        }

        false
    }

    // Puts the parent object to the gray again queue
    // if it's black and the current phase of the gc cycle is `Marking`
    //
    // this allows for mutating a parent object and adding child pointers to it
    // as they will be traced and handled by the garbage collector.
    fn barrier(&self, parent: GcBox) {
        if let GcState::Marking = self.state
            && let GcColor::Black = parent.header().color.get()
        {
            self.put_to_gray_again_queue(parent);
        }
    }
}

impl<'gc> Trace<'gc> for Cx {
    fn trace_gc(&mut self, gc: Gc<'gc, ()>) {
        let gcbox = unsafe { gc.get_gc_box() };

        let header = gcbox.header();

        match header.color.get() {
            GcColor::Black | GcColor::Gray => {}

            GcColor::White => {
                if header.needs_trace.get() {
                    self.gray_objects.push(gcbox);

                    header.color.set(GcColor::Gray);
                } else {
                    header.color.set(GcColor::Black);
                }
            }
        }
    }
}

#[derive(Debug)]
struct Vtable {
    trace_self: unsafe fn(GcBox, &mut Cx),
    drop: unsafe fn(GcBox),
    layout: core::alloc::Layout,
}

impl Vtable {
    pub const fn new_for<'gc, T: ToHeap<'gc>>() -> Vtable {
        Self {
            layout: Layout::new::<TypedGcBox<T>>(),
            trace_self: |ptr, cx| unsafe {
                let actual = ptr.ptr_to_value::<T>().as_ref();
                actual.trace(cx);
            },
            drop: |ptr| unsafe {
                ptr::drop_in_place(ptr.ptr_to_value::<T>().as_ptr());
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GcColor {
    White,
    Gray,
    Black,
}

#[derive(Debug)]
pub(crate) struct Header {
    next: Cell<Option<GcBox>>,

    vtable: &'static Vtable,

    color: Cell<GcColor>,

    live: Cell<bool>,

    needs_trace: Cell<bool>,
}

impl Header {
    pub fn new<'gc, T: ToHeap<'gc>>() -> Self {
        trait HasVtable {
            const VTABLE: Vtable;
        }

        impl<'gc, T: ToHeap<'gc>> HasVtable for T {
            const VTABLE: Vtable = Vtable::new_for::<T>();
        }

        let vtable: &'static Vtable = &T::VTABLE;

        Self {
            next: Cell::new(None),
            vtable,
            color: Cell::new(GcColor::White),
            needs_trace: Cell::new(true),
            live: Cell::new(false),
        }
    }

    pub fn box_size(&self) -> usize {
        self.vtable.layout.size()
    }

    pub fn change_color(&self, color: GcColor) {
        self.color.set(color);
    }

    pub fn set_live(&self, liveness: bool) {
        self.live.set(liveness);
    }

    pub fn set_needs_trace(&self, need: bool) {
        self.needs_trace.set(need);
    }
}

pub(crate) struct TypedGcBox<T: ?Sized> {
    header: Header,
    pub data: ManuallyDrop<T>,
}

impl<'gc, T: ToHeap<'gc>> TypedGcBox<T> {
    pub fn new(header: Header, data: T) -> Self {
        Self {
            header,
            data: ManuallyDrop::new(data),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct GcBox {
    ptr: NonNull<TypedGcBox<()>>,
}

impl GcBox {
    pub fn new(ptr: NonNull<TypedGcBox<()>>) -> Self {
        Self { ptr }
    }

    pub unsafe fn ptr_to_value<T>(&self) -> NonNull<T> {
        let inner = self.ptr.cast::<TypedGcBox<T>>();

        unsafe {
            let ptr = ptr::addr_of_mut!((*inner.as_ptr()).data).cast::<T>();
            NonNull::new_unchecked(ptr)
        }
    }

    fn header(&self) -> &Header {
        unsafe { &self.ptr.as_ref().header }
    }

    pub unsafe fn erase_type<'gc, T>(ptr: NonNull<TypedGcBox<T>>) -> GcBox
    where
        T: ToHeap<'gc>,
    {
        GcBox { ptr: ptr.cast() }
    }

    pub unsafe fn deallocate(self) {
        let header = self.header();
        let layout = header.vtable.layout;

        unsafe {
            let value: *mut u8 = self.ptr.as_ptr().cast();
            dealloc(value, layout);
        }
    }

    pub unsafe fn drop_in_place(self) {
        unsafe { (self.ptr.as_ref().header.vtable.drop)(self) }
    }

    pub fn trace_self(self, cx: &mut Cx) {
        unsafe { (self.ptr.as_ref().header.vtable.trace_self)(self, cx) }
    }
}

struct Queue<T> {
    inner: core::cell::UnsafeCell<Vec<T>>,
}

impl<T> Queue<T> {
    fn new() -> Self {
        Self {
            inner: core::cell::UnsafeCell::new(Vec::new()),
        }
    }

    fn push(&self, item: T) {
        unsafe { (*self.inner.get()).push(item) };
    }

    fn pop(&self) -> Option<T> {
        unsafe { (*self.inner.get()).pop() }
    }
}
