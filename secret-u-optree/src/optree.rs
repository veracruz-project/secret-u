//! Core lazy-AST and compiler

use std::rc::Rc;
use std::fmt::Debug;
use std::fmt::LowerHex;
use std::io;
use std::convert::TryFrom;
use std::fmt;
use std::cell::Cell;
use std::cmp::max;
use std::mem::size_of;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::hash::Hasher;
use std::borrow::Borrow;
#[cfg(feature="opt-color-slots")]
use std::collections::BTreeSet;
use std::cmp::Ordering;
use std::cell::RefCell;
use std::ops::Deref;
use std::ops::DerefMut;
use std::borrow::Cow;

use secret_u_opcode::Error;
use secret_u_opcode::OpCode;
use secret_u_opcode::OpIns;
use secret_u_opcode::prefix;
#[cfg(feature="debug-bytecode")]
use secret_u_opcode::disas;
use crate::engine::exec;

use secret_u_macros::for_secret_t;

use aligned_utils::bytes::AlignedBytes;


/// Abritrary names for dissassembly
fn arbitrary_names() -> impl Iterator<Item=String> {
    let alphabet = "abcdefghijklmnopqrstuvwxyz";
    // a..z
    alphabet.chars()
        .map(move |c| String::from(c))
        .chain(
            // a2..z2, a3..z3, ...
            (2..).map(move |n| {
                    alphabet.chars()
                        .map(move |c| format!("{}{}", c, n))
                })
                .flatten()
        )
}

/// Hack for reborrowing Options containing mut refs
trait Reborrow {
    type Reborrow;

    fn reborrow(self) -> Self::Reborrow;
}

impl<'a, 'b, T> Reborrow for &'b mut Option<&'a mut T> {
    type Reborrow = Option<&'b mut T>;

    fn reborrow(self) -> Self::Reborrow {
        self.as_mut().map(|x| &mut **x)
    }
}

/// Trait for the underlying raw types
pub trait OpU: Default + Copy + Clone + Debug + LowerHex + Eq + Sized + 'static {
    /// npw2(size)
    const NPW2: u8;

    /// raw byte representation
    type Bytes: AsRef<[u8]> + AsMut<[u8]> + for<'a> TryFrom<&'a [u8]>;

    /// access the underlying raw bytes
    fn as_ne_bytes(&self) -> &[u8];

    /// to raw byte representation
    fn to_le_bytes(self) -> Self::Bytes;

    /// from raw byte representation
    fn from_le_bytes(bytes: Self::Bytes) -> Self;

    /// Zero
    fn zero() -> Self;

    /// One
    fn one() -> Self;

    /// All bits set to one
    fn ones() -> Self;

    /// Unsign-extend a smaller type
    fn extend_u<U: OpU>(other: U) -> Self;

    /// Sign-extend a smaller type
    fn extend_s<U: OpU>(other: U) -> Self;

    /// Splat a smaller type
    fn splat<U: OpU>(other: U) -> Self;

    /// Test if self is zero
    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }

    /// Test if self is one
    fn is_one(&self) -> bool {
        self == &Self::one()
    }

    /// Test if self is ones
    fn is_ones(&self) -> bool {
        self == &Self::ones()
    }

    /// Can we compress into a sign-extend followed by a splat?
    fn is_extend_splat(&self, extend_npw2: u8, splat_npw2: u8) -> bool {
        let bytes = self.to_le_bytes();
        let bytes = bytes.as_ref();
        let splat_width = 1usize << splat_npw2;
        let extend_width = 1usize << extend_npw2;

        // is extend?
        (splat_width..bytes.len())
            .step_by(splat_width)
            .all(|i| &bytes[i..i+splat_width] == &bytes[..splat_width])
            // is extend?
            && if bytes[extend_width-1] & 0x80 == 0x80 {
                bytes[extend_width..splat_width].iter().all(|b| *b == 0xff)
            } else {
                bytes[extend_width..splat_width].iter().all(|b| *b == 0x00)
            }
    }

    /// Find the smallest sign-extend splat representation
    fn find_extend_splat(&self) -> (u8, u8) {
        // find best splat
        for splat_npw2 in 0..=Self::NPW2 {
            if self.is_extend_splat(splat_npw2, splat_npw2) {
                // find best extend-splat
                for extend_npw2 in 0..=splat_npw2 {
                    if self.is_extend_splat(extend_npw2, splat_npw2) {
                        return (extend_npw2, splat_npw2);
                    }
                }
            }
        }

        unreachable!();
    }
}




for_secret_t! {
    __if(__t == "u") {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct __U([u8; __size]);

        impl From<[u8; __size]> for __U {
            fn from(v: [u8; __size]) -> Self {
                Self::from_le_bytes(v)
            }
        }

        impl From<__U> for [u8; __size] {
            fn from(v: __U) -> [u8; __size] {
                v.to_le_bytes()
            }
        }

        __if(__has_prim) {
            impl From<__prim_u> for __U {
                fn from(v: __prim_u) -> Self {
                    Self::from_le_bytes(v.to_le_bytes())
                }
            }

            impl From<__U> for __prim_u {
                fn from(v: __U) -> __prim_u {
                    <__prim_u>::from_le_bytes(v.to_le_bytes())
                }
            }

            impl From<__prim_i> for __U {
                fn from(v: __prim_i) -> Self {
                    Self::from_le_bytes(v.to_le_bytes())
                }
            }

            impl From<__U> for __prim_i {
                fn from(v: __U) -> __prim_i {
                    <__prim_i>::from_le_bytes(v.to_le_bytes())
                }
            }
        }

        impl OpU for __U {
            const NPW2: u8 = __npw2;

            type Bytes = [u8; __size];

            fn as_ne_bytes(&self) -> &[u8] {
                &self.0
            }

            fn to_le_bytes(self) -> Self::Bytes {
                self.0
            }

            fn from_le_bytes(bytes: Self::Bytes) -> Self {
                Self(bytes)
            }

            fn zero() -> Self {
                Self([0; __size])
            }

            fn one() -> Self {
                let mut bytes = [0; __size];
                bytes[0] = 1;
                Self(bytes)
            }

            fn ones() -> Self {
                Self([0xff; __size])
            }

            fn extend_u<U: OpU>(other: U) -> Self {
                let slice = other.to_le_bytes();
                let slice = slice.as_ref();
                let mut bytes = [0; __size];
                bytes[..slice.len()].copy_from_slice(slice);
                Self(bytes)
            }

            fn extend_s<U: OpU>(other: U) -> Self {
                let slice = other.to_le_bytes();
                let slice = slice.as_ref();
                let mut bytes = if slice[slice.len()-1] & 0x80 == 0x80 {
                    [0xff; __size]
                } else {
                    [0x00; __size]
                };
                bytes[..slice.len()].copy_from_slice(slice);
                Self(bytes)
            }

            fn splat<U: OpU>(other: U) -> Self {
                let slice = other.to_le_bytes();
                let slice = slice.as_ref();
                let mut bytes = [0; __size];
                for i in (0..__size).step_by(slice.len()) {
                    bytes[i..i+slice.len()].copy_from_slice(slice);
                }
                Self(bytes)
            }
        }

        impl Default for __U {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl LowerHex for __U {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                write!(fmt, "0x")?;
                for b in self.0.iter().rev() {
                    write!(fmt, "{:02x}", b)?;
                }
                Ok(())
            }
        }
    }
}


/// Kinds of operations in tree
#[derive(Debug)]
pub enum OpKind<T: OpU> {
    Const(T),
    Imm(T),
    Sym(&'static str),

    Extract(u16, RefCell<Rc<dyn DynOpNode>>),
    Replace(u16, RefCell<Rc<OpNode<T>>>, RefCell<Rc<dyn DynOpNode>>),
    Select(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Shuffle(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),

    ExtendU(u8, RefCell<Rc<dyn DynOpNode>>),
    ExtendS(u8, RefCell<Rc<dyn DynOpNode>>),
    Truncate(u8, RefCell<Rc<dyn DynOpNode>>),
    Splat(RefCell<Rc<dyn DynOpNode>>),

    Eq(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Ne(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    LtU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    LtS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    GtU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    GtS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    LeU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    LeS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    GeU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    GeS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    MinU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    MinS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    MaxU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    MaxS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),

    Neg(u8, RefCell<Rc<OpNode<T>>>),
    Abs(u8, RefCell<Rc<OpNode<T>>>),
    Not(RefCell<Rc<OpNode<T>>>),
    Clz(u8, RefCell<Rc<OpNode<T>>>),
    Ctz(u8, RefCell<Rc<OpNode<T>>>),
    Popcnt(u8, RefCell<Rc<OpNode<T>>>),
    Add(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Sub(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Mul(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    And(RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Andnot(RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Or(RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Xor(RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Shl(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    ShrU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    ShrS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Rotl(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Rotr(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
}


/// Tree of operations, including metadata to deduplicate
/// common branches
#[derive(Debug)]
pub struct OpNode<T: OpU> {
    kind: OpKind<T>,
    refs: Cell<u32>,
    slot: Cell<Option<u16>>,
    flags: u8,
    #[cfg(feature="opt-schedule-slots")]
    depth: u32,
    #[cfg(feature="opt-fold-consts")]
    folded: Cell<bool>,
}

/// Root OpNode with additional small object optimization, which
/// is useful for avoiding unnecessary allocations
///
/// Note this still participates in DAG deduplication by lazily
/// allocating on demand, the result is a lot of RefCells...
///
/// Also not that Cell is not usable here because Rc does not
/// implement Copy
///
#[derive(Debug)]
pub struct OpTree<T: OpU>(RefCell<OpRoot<T>>);

#[derive(Debug)]
pub enum OpRoot<T: OpU> {
    Const(T),
    Imm(T),
    Tree(Rc<OpNode<T>>),
}

impl<T: OpU> Default for OpTree<T> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<T: OpU> Clone for OpTree<T> {
    // clone defers to tree, which ensures the backing tree is
    // Rc before cloning
    fn clone(&self) -> Self {
        OpTree(RefCell::new(OpRoot::Tree(self.node())))
    }
}


/// Pool of const OpNodes
#[derive(Debug)]
pub struct ConstPool {
    pool: HashSet<ConstPoolNode>
}

/// Wrapper around OpNode for hashing const nodes
#[derive(Debug)]
struct ConstPoolNode(Rc<dyn DynOpNode>);

impl PartialEq<ConstPoolNode> for ConstPoolNode {
    fn eq(&self, other: &ConstPoolNode) -> bool {
        self.0.get_const_ne_bytes() == other.0.get_const_ne_bytes()
    }
}

impl Eq for ConstPoolNode {}

impl Hash for ConstPoolNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.get_const_ne_bytes().hash(state)
    }
}

impl Borrow<[u8]> for ConstPoolNode {
    fn borrow(&self) -> &[u8] {
        self.0.get_const_ne_bytes().unwrap()
    }
}

impl ConstPool {
    pub fn new() -> ConstPool {
        ConstPool {
            pool: HashSet::new()
        }
    }

    pub fn deduplicate(&mut self, node: &Rc<dyn DynOpNode>) -> Option<Rc<dyn DynOpNode>> {
        debug_assert!(node.is_const());

        // already exists?
        if let Some(node) = self.pool.get(node.get_const_ne_bytes().unwrap()) {
            return Some(node.0.clone());
        }

        // insert new node
        self.pool.insert(ConstPoolNode(node.clone()));
        None
    }

    pub fn deduplicate_new<T: OpU>(&mut self, v: T) -> Rc<dyn DynOpNode> {
        // already exists?
        if let Some(node) = self.pool.get(v.as_ne_bytes()) {
            return node.0.clone();
        }

        // insert new node
        let node = Rc::new(OpNode::<T>::new(
            OpKind::Const(v), 0, 0
        ));
        self.pool.insert(ConstPoolNode(node.clone()));
        node
    }
}

/// Pool for allocating/reusing slots in a fictional blob of bytes
#[derive(Debug)]
struct SlotPool {
    // pool of deallocated slots
    #[cfg(feature="opt-color-slots")]
    pool: BTreeSet<SlotPoolSlot>,

    // current end of blob
    size: usize,

    // aligned of blob
    max_npw2: u8,
}

/// Slot in the slot pool, ordered first by slot size,
/// and second by decreasing slot numbers
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
struct SlotPoolSlot(u8, u16);
//                  ^   ^- slot number
//                  '----- slot npw2

impl PartialOrd for SlotPoolSlot {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SlotPoolSlot {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
            .then_with(|| self.1.cmp(&other.1).reverse())
    }
}


impl SlotPool {
    /// Create a new empty slot pool
    pub fn new() -> SlotPool {
        SlotPool {
            #[cfg(feature="opt-color-slots")]
            pool: BTreeSet::new(),
            size: 0,
            max_npw2: 0,
        }
    }

    /// Allocate a slot with the required npw2 size,
    /// note it's possible to run out of slots here
    pub fn alloc(&mut self, npw2: u8) -> Result<u16, Error> {
        // The allocation scheme here is a bit complicated.
        //
        // Slots of all sizes share a common buffer, which means
        // smaller slots have a smaller addressable range than larger
        // slots.
        //
        //  .--------- u32 slot 0
        //  v       v- u32 slot 1
        // [ | | | | | | | | ...
        //  ^-^------- u8 slot 0
        //    '------- u8 slot 1
        //
        // An optimal algorithm would probably allocate all slots and
        // then sort by size, but since we're only doing this in one pass
        // we just try to avoid the lower ranges of slots as much as possible.
        //
        // This includes:
        // 1. Reusing slots from the largest already-allocated slot of a
        //    give size
        // 2. Limiting slot 0 to u8 slots
        //

        #[cfg(feature="opt-color-slots")]
        {
            // find smallest slot where size >= npw2 but slot*size < 256
            let best_slot = self.pool.range(SlotPoolSlot(npw2, u16::MAX)..)
                .copied()
                .filter(|SlotPoolSlot(best_npw2, best_slot)| {
                    // fits in slot number?
                    u16::try_from(
                        (usize::from(*best_slot) << best_npw2) >> npw2
                    ).is_ok()
                })
                .next();
            if let Some(SlotPoolSlot(mut best_npw2, mut best_slot)) = best_slot {
                // remove from pool
                self.pool.remove(&SlotPoolSlot(best_npw2, best_slot));

                // pad
                while best_npw2 > npw2 {
                    best_slot *= 2;
                    best_npw2 -= 1;
                    // return padding into pool
                    if let Some(padding_slot) = best_slot.checked_add(1) {
                        self.dealloc(best_npw2, padding_slot);
                    }
                }

                debug_assert!(best_npw2 == npw2);
                self.max_npw2 = max(self.max_npw2, npw2);
                return Ok(best_slot)
            }
        }


        // no slot found? fallback to increasing size of our slot pool

        // skip slot 0?
        if self.size == 0 && npw2 != 0 {
            self.size += 1;
            self.dealloc(0, 0);
        }

        // allocate new slot
        while self.size % (1 << npw2) != 0 {
            let padding_npw2 = self.size.trailing_zeros();
            let padding_slot = self.size >> padding_npw2;
            self.size += 1 << padding_npw2;
            if let Ok(padding_slot) = u16::try_from(padding_slot) {
                self.dealloc(u8::try_from(padding_npw2).unwrap(), padding_slot);
            }
        }

        match u16::try_from(self.size >> npw2) {
            Ok(slot) => {
                self.size += 1 << npw2;
                self.max_npw2 = max(self.max_npw2, npw2);
                Ok(slot)
            }
            _ => {
                Err(Error::OutOfSlots(npw2))
            }
        }
    }

    /// Return a slot to the pool
    pub fn dealloc(
        &mut self,
        #[allow(unused)] mut npw2: u8,
        #[allow(unused)] mut slot: u16
    ) {
        // do nothing here if we aren't reusing slots
        #[cfg(feature="opt-color-slots")]
        {
            // don't defragment slot 0! reserved for a u8, this
            // intentionally fragments the front of our pool, which
            // helps keep us from clobbering smaller slots with one
            // big one
            if slot & !1 != 0 {
                // try to defragment?
                while self.pool.remove(&SlotPoolSlot(npw2, slot ^ 1)) {
                    slot /= 2;
                    npw2 += 1;
                }
            }

            assert!(
                self.pool.insert(SlotPoolSlot(npw2, slot)),
                "Found duplicate slot in pool!? ({}, {})\n{:?}",
                npw2, slot,
                self.pool
            )
        }
    }
}

/// Compilation state
pub struct OpCompile {
    bytecode: Vec<u64>,
    state: Vec<u8>,

    #[allow(dead_code)]
    opt: bool,
    slot_pool: SlotPool,
}

impl OpCompile {
    pub fn new(opt: bool) -> OpCompile {
        OpCompile {
            bytecode: Vec::new(),
            state: Vec::new(),

            opt: opt,
            slot_pool: SlotPool::new(),
        }
    }
}


/// A trait to help with conversions between trees of different types
pub trait DynOpTree {
    /// get NPW2 of the underlying tree
    fn npw2(&self) -> u8;

    /// get the underlying DynOpNode
    fn dyn_node(&self) -> Rc<dyn DynOpNode>;

    // some dyn operations that can avoid casting
    fn dyn_not(&self) -> Rc<dyn DynOpTree>;
    fn dyn_and(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
    fn dyn_andnot(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
    fn dyn_notand(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
    fn dyn_or(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
    fn dyn_xor(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
}

impl<T: OpU> DynOpTree for OpTree<T> {
    fn npw2(&self) -> u8 {
        T::NPW2
    }

    fn dyn_node(&self) -> Rc<dyn DynOpNode> {
        // node triggers a lazily allocated Rc object here, and then
        // we insert our trait object as we return, neato
        self.node()
    }

    fn dyn_not(&self) -> Rc<dyn DynOpTree> {
        Rc::new(Self::not(self.clone()))
    }

    fn dyn_and(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_and(self)
        } else {
            Rc::new(Self::and(self.clone(), OpTree::dyn_cast_s(other).into_owned()))
        }
    }

    fn dyn_andnot(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_notand(self)
        } else {
            Rc::new(Self::andnot(self.clone(), OpTree::dyn_cast_s(other).into_owned()))
        }
    }

    fn dyn_notand(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_andnot(self)
        } else {
            Rc::new(Self::andnot(OpTree::dyn_cast_s(other).into_owned(), self.clone()))
        }
    }

    fn dyn_or(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_or(self)
        } else {
            Rc::new(Self::or(self.clone(), OpTree::dyn_cast_s(other).into_owned()))
        }
    }

    fn dyn_xor(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_xor(self)
        } else {
            Rc::new(Self::xor(self.clone(), OpTree::dyn_cast_s(other).into_owned()))
        }
    }
}

/// Core of the OpTree
impl<T: OpU> OpTree<T> {
    /// Create an immediate, secret value
    pub fn imm<U>(v: U) -> Self
    where
        T: From<U>
    {
        OpTree(RefCell::new(OpRoot::Imm(T::from(v))))
    }

    /// Create a const susceptable to compiler optimizations
    pub fn const_<U>(v: U) -> Self
    where
        T: From<U>
    {
        OpTree(RefCell::new(OpRoot::Const(T::from(v))))
    }

    /// A constant 0
    pub fn zero() -> Self {
        Self::const_(T::zero())
    }

    /// A constant 1
    pub fn one() -> Self {
        Self::const_(T::one())
    }

    /// A constant with all bits set to 1
    pub fn ones() -> Self {
        Self::const_(T::ones())
    }

    /// Create new tree
    fn from_kind(kind: OpKind<T>, flags: u8, depth: u32) -> Self {
        OpTree(RefCell::new(OpRoot::Tree(Rc::new(
            OpNode::new(kind, flags, depth)
        ))))
    }

    /// Get internal tree, potentially allocating if needed
    fn node(&self) -> Rc<OpNode<T>> {
        let mut tree = self.0.borrow_mut();
        match tree.deref() {
            OpRoot::Const(v) => {
                // convert to Rc if necessary
                let node = Rc::new(OpNode::new(
                    OpKind::Const(*v), 0, 0
                ));
                *tree = OpRoot::Tree(node.clone());
                node
            }
            OpRoot::Imm(v) => {
                // convert to Rc if necessary
                let node = Rc::new(OpNode::new(
                    OpKind::Imm(*v), OpNode::<T>::SECRET, 0
                ));
                *tree = OpRoot::Tree(node.clone());
                node
            }
            OpRoot::Tree(node) => {
                // can just increment reference count here
                node.clone()
            }
        }
    }

    /// Forcefully downcast into a different OpTree, panicking if types
    /// do not match
    pub fn dyn_downcast<'a>(a: &'a dyn DynOpTree) -> &'a Self {
        assert_eq!(a.npw2(), T::NPW2);
        unsafe { &*(a as *const dyn DynOpTree as *const Self) }
    }

    /// Helper for choosing the most efficient cast between trees of
    /// different types, including returning the tree as is with only
    /// the type information stripped
    pub fn dyn_cast_u<'a>(a: &'a dyn DynOpTree) -> Cow<'a, Self> {
        if T::NPW2 > a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Cow::Owned(Self::from_kind(OpKind::ExtendU(0, RefCell::new(a)), flags, depth))
        } else if T::NPW2 < a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Cow::Owned(Self::from_kind(OpKind::Truncate(0, RefCell::new(a)), flags, depth))
        } else {
            Cow::Borrowed(Self::dyn_downcast(a))
        }
    }

    /// Helper for choosing the most efficient cast between trees of
    /// different types, including returning the tree as is with only
    /// the type information stripped
    pub fn dyn_cast_s<'a>(a: &'a dyn DynOpTree) -> Cow<'a, Self> {
        if T::NPW2 > a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Cow::Owned(Self::from_kind(OpKind::ExtendS(0, RefCell::new(a)), flags, depth))
        } else if T::NPW2 < a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Cow::Owned(Self::from_kind(OpKind::Truncate(0, RefCell::new(a)), flags, depth))
        } else {
            Cow::Borrowed(Self::dyn_downcast(a))
        }
    }

    /// is expression an immediate?
    pub fn is_imm(&self) -> bool {
        match self.0.borrow().deref() {
            OpRoot::Const(_) => true,
            OpRoot::Imm(_) => true,
            OpRoot::Tree(tree) => tree.is_imm(),
        }
    }

    /// is expression a symbol?
    pub fn is_sym(&self) -> bool {
        match self.0.borrow().deref() {
            OpRoot::Const(_) => false,
            OpRoot::Imm(_) => false,
            OpRoot::Tree(tree) => tree.is_sym(),
        }
    }

    /// is expression const?
    pub fn is_const(&self) -> bool {
        match self.0.borrow().deref() {
            OpRoot::Const(_) => true,
            OpRoot::Imm(_) => false,
            OpRoot::Tree(tree) => tree.is_const(),
        }
    }

    // Constructors for other tree nodes, note that
    // constant-ness is propogated
    pub fn sym(name: &'static str) -> Self {
        Self::from_kind(OpKind::Sym(name), OpNode::<T>::SECRET | OpNode::<T>::SYM, 0)
    }

    pub fn extract<U: OpU>(x: u16, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Extract(x, RefCell::new(a)), flags, depth)
    }

    pub fn replace<U: OpU>(x: u16, a: Self, b: OpTree<U>) -> Self {
        let a = a.node();
        let b = b.dyn_node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Replace(x, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn select(lnpw2: u8, p: Self, a: Self, b: Self) -> Self {
        let p = p.node();
        let a = a.node();
        let b = b.node();
        let flags = p.flags() | a.flags() | b.flags();
        let depth = max(p.depth(), max(a.depth(), b.depth())).saturating_add(1);
        Self::from_kind(OpKind::Select(lnpw2, RefCell::new(p), RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn shuffle(lnpw2: u8, p: Self, a: Self, b: Self) -> Self {
        let p = p.node();
        let a = a.node();
        let b = b.node();
        let flags = p.flags() | a.flags() | b.flags();
        let depth = max(p.depth(), max(a.depth(), b.depth())).saturating_add(1);
        Self::from_kind(OpKind::Shuffle(lnpw2, RefCell::new(p), RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn extend_u<U: OpU>(lnpw2: u8, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::ExtendU(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn extend_s<U: OpU>(lnpw2: u8, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::ExtendS(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn truncate<U: OpU>(lnpw2: u8, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Truncate(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn splat<U: OpU>(a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Splat(RefCell::new(a)), flags, depth)
    }

    pub fn eq(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Eq(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn ne(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Ne(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn lt_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LtU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn lt_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LtS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn gt_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GtU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn gt_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GtS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn le_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LeU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn le_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LeS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn ge_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GeU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn ge_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GeS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn min_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MinU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn min_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MinS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn max_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MaxU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn max_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MaxS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn neg(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Neg(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn abs(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Abs(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn not(a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Not(RefCell::new(a)), flags, depth)
    }

    pub fn clz(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Clz(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn ctz(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Ctz(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn popcnt(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Popcnt(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn add(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Add(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn sub(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Sub(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn mul(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Mul(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn and(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::And(RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn andnot(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Andnot(RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn or(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Or(RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn xor(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Xor(RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn shl(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Shl(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn shr_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::ShrU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn shr_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::ShrS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn rotl(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Rotl(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn rotr(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Rotr(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    /// display tree for debugging
    pub fn disas<W: io::Write>(&self, mut out: W) -> Result<(), io::Error> {
        match self.0.borrow().deref() {
            OpRoot::Const(v) => writeln!(out, "    (u{}.const {:x}", 8 << T::NPW2, v),
            OpRoot::Imm(v)   => writeln!(out, "    (u{}.imm {:x})",  8 << T::NPW2, v),
            OpRoot::Tree(tree) => tree.disas(out),
        }
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self, opt: bool) -> (Vec<u64>, AlignedBytes) {
        // force to tree form
        self.node();

        match self.0.borrow_mut().deref_mut() {
            OpRoot::Tree(ref mut tree) => {
                // should we do a constant folding pass? we need to do this here
                // so we can update our root reference
                #[cfg(feature="opt-fold-consts")]
                if opt {
                    #[cfg(feature="opt-deduplicate-consts")]
                    let mut const_pool = Some(ConstPool::new());
                    #[cfg(not(feature="opt-deduplicate-consts"))]
                    let const_pool = None;

                    let tree_dyn: Rc<dyn DynOpNode> = tree.clone();
                    if let Some(x) = tree.fold_consts(&tree_dyn, const_pool.as_mut()) {
                        *tree = OpNode::<T>::dyn_downcast(x);
                    }
                }

                // compile
                tree.compile(opt)
            }
            _ => panic!("compiling non-tree?"),
        }
    }

    /// Assuming we are Sym, patch the state during a call
    pub fn patch<U>(&self, state: &mut [u8], v: U)
    where
        T: From<U>
    {
        match self.0.borrow().deref() {
            OpRoot::Tree(tree) => tree.patch(state, v),
            _ => panic!("patching non-sym?")
        }
    }

    /// execute bytecode, resulting in an immediate OpTree
    pub fn exec(bytecode: &[u64], state: &mut [u8]) -> Self {
        Self::try_exec(bytecode, state).unwrap()
    }

    /// execute bytecode, resulting in an immediate OpTree
    pub fn try_exec(bytecode: &[u64], state: &mut [u8]) -> Result<Self, Error> {
        let res = exec(bytecode, state)?;
        Ok(OpTree(RefCell::new(OpRoot::Imm(T::from_le_bytes(
            T::Bytes::try_from(res).map_err(|_| Error::InvalidReturn)?
        )))))
    }

    /// compile and execute if OpTree is not already an immediate
    pub fn eval(&self) -> Self {
        self.try_eval().unwrap()
    }

    /// compile and execute if OpTree is not already an immediate
    pub fn try_eval(&self) -> Result<Self, Error> {
        match self.0.borrow().deref() {
            OpRoot::Const(v) => Ok(Self::const_(*v)),
            OpRoot::Imm(v)   => Ok(Self::imm(*v)),
            OpRoot::Tree(tree) => {
                if tree.is_sym() {
                    Err(Error::DeclassifyInCompile)?;
                }

                let (bytecode, mut stack) = tree.compile(false);
                Self::try_exec(&bytecode, &mut stack)
            }
        }
    }

    /// retrieve result, panicking if OpTree is not in immediate form
    pub fn result<U>(self) -> U
    where
        U: From<T>
    {
        self.try_result::<U>()
            .expect("attempted to get result from un-evaled tree")
    }

    /// retrieve result, or None
    pub fn try_result<U>(self) -> Option<U>
    where
        U: From<T>
    {
        match self.0.into_inner() {
            OpRoot::Const(v) => Some(U::from(v)),
            OpRoot::Imm(v)   => Some(U::from(v)),
            OpRoot::Tree(_)  => None,
        }
    }
}

/// Core OpNode type
impl<T: OpU> OpNode<T> {
    const SECRET: u8 = 0x1;
    const SYM: u8    = 0x2;

    fn new(kind: OpKind<T>, flags: u8, #[allow(unused)] depth: u32) -> OpNode<T> {
        OpNode {
            kind: kind,
            refs: Cell::new(0),
            slot: Cell::new(None),
            flags: flags,
            #[cfg(feature="opt-schedule-slots")]
            depth: depth,
            #[cfg(feature="opt-fold-consts")]
            folded: Cell::new(false),
        }
    }

    /// Forcefully downcast into a different OpNode, panicking if types
    /// do not match
    pub fn dyn_downcast(a: Rc<dyn DynOpNode>) -> Rc<Self> {
        assert_eq!(a.npw2(), T::NPW2);
        unsafe { Rc::from_raw(Rc::into_raw(a) as _) }
    }

    /// display tree for debugging
    pub fn disas<W: io::Write>(&self, mut out: W) -> Result<(), io::Error> {
        // get a source of variable names, these represent
        // deduplicate dag branches
        let mut slot_names = HashMap::new();
        let mut arbitrary_names = arbitrary_names();

        // two passes, since we want to deduplicate the dag, otherwise
        // our debug output gets VERY BIG
        self.disas_pass1();
        let expr = self.disas_pass2(
            &mut slot_names,
            &mut arbitrary_names,
            &mut out
        )?;

        #[cfg(feature="debug-check-refs")]
        self.check_refs();

        // cleanup last expression
        write!(out, "    {}\n", expr)
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self, opt: bool) -> (Vec<u64>, AlignedBytes) {
        // debug?
        #[cfg(feature="debug-ast")]
        {
            println!("tree:");
            self.disas(io::stdout()).unwrap();
        }

        // NOTE! We make sure to zero all refs from pass1 to pass2, this is
        // rather fragile and requires all passes to always be run as a pair,
        // we can't interrupt between passes without needing to reset all
        // internal reference counts

        let mut state = OpCompile::new(opt);

        // first pass to find number of immediates and deduplicate branches
        self.compile_pass1(&mut state);

        // second pass now to compile the bytecode and stack, note sp now points
        // to end of immediates
        let (_, slot) = self.compile_pass2(&mut state);

        // to make lifetimes work in order to figure out slot reuse, reference
        // counting for is left up to the caller
        let refs = self.dec_refs();
        debug_assert_eq!(refs, 0);

        #[cfg(feature="debug-check-refs")]
        self.check_refs();

        // add required return instruction
        state.bytecode.push(u64::from(OpIns::new(
            T::NPW2, 0, OpCode::Ret, 0, slot, 0
        )));

        // align state
        let mut aligned_state = AlignedBytes::new_zeroed(
            state.slot_pool.size,
            1usize << state.slot_pool.max_npw2
        );
        aligned_state[..state.state.len()].copy_from_slice(&state.state);

        #[cfg(feature="debug-bytecode")]
        {
            println!("state:");
            print!("   ");
            for b in aligned_state.iter() {
                 print!(" {:02x}", b);
            }
            println!();

            println!("bytecode:");
            disas(&state.bytecode, io::stdout()).unwrap();
        }

        // imms is now the initial stack pointer
        (state.bytecode, aligned_state)
    }

    /// Assuming we are Sym, patch the state during a call
    pub fn patch<U>(&self, state: &mut [u8], v: U)
    where
        T: From<U>
    {
        assert!(
            match self.kind {
                OpKind::Sym(_) => true,
                _              => false,
            },
            "patching non-sym?"
        );

        let slot = self.slot.get().expect("patching with no slot?");
        state[
            slot as usize * size_of::<T>()
                .. (slot as usize + 1) * size_of::<T>()
        ].copy_from_slice(T::from(v).to_le_bytes().as_ref());
    }

    /// compile and execute if value is not already an immediate or constant
    pub fn eval(&self) -> T {
        self.try_eval().unwrap()
    }

    /// compile and execute if value is not already an immediate or constant
    pub fn try_eval(&self) -> Result<T, Error> {
        let (bytecode, mut stack) = self.compile(false);
        Ok(OpTree::try_exec(&bytecode, &mut stack)?.result())
    }
}

// dyn-compatible wrapping trait
pub trait DynOpNode: Debug {
    /// npw2(size), used as a part of instruction encoding
    fn npw2(&self) -> u8;

    /// bitwised-or flags from all branches
    fn flags(&self) -> u8;

    /// saturating depth of tree for heuristic purposes
    fn depth(&self) -> u32;

    /// is expression an immediate?
    fn is_imm(&self) -> bool;

    /// is expression a symbol?
    fn is_sym(&self) -> bool;

    /// is expression const?
    fn is_const(&self) -> bool;

    /// checks if expression is const and is zero
    fn is_const_zero(&self) -> bool;

    /// checks if expression is const and is one
    fn is_const_one(&self) -> bool;

    /// checks if expression is const and is ones
    fn is_const_ones(&self) -> bool;

    /// checks if expression is compressable into a u16
    fn is_const_u16(&self, lnpw2: Option<u8>) -> bool;

    /// checks if expression is compressable into a u16
    fn get_const_u16(&self, lnpw2: Option<u8>) -> Option<(u8, u16)>;

    /// get raw value of underlying const if node is const, note
    /// because of trait object limitations we can't get the
    /// type-safe type, so this should only be used for things like
    /// hashing/equality checking
    fn get_const_ne_bytes<'a>(&'a self) -> Option<&'a [u8]>;

    /// Increment tree-internal reference count
    fn inc_refs(&self) -> u32;

    /// Decrement tree-internal reference count
    fn dec_refs(&self) -> u32;

    /// First pass for debug output
    fn disas_pass1(&self);

    /// Second pass for debug output
    fn disas_pass2(
        &self,
        names: &mut HashMap<usize, String>,
        arbitrary_names: &mut dyn Iterator<Item=String>,
        stmts: &mut dyn io::Write,
    ) -> Result<String, io::Error>;

    /// Optional pass to check that refs return to 0
    ///
    /// Note this is very expensive
    #[cfg(feature="debug-check-refs")]
    fn check_refs(&self);

    /// An optional pass to fold consts in the tree
    #[cfg(feature="opt-fold-consts")]
    fn fold_consts(
        &self,
        rc: &Rc<dyn DynOpNode>,
        const_pool: Option<&mut ConstPool>
    ) -> Option<Rc<dyn DynOpNode>>;

    /// First compile pass, used to find the number of immediates
    /// for offset calculation, and local reference counting to
    /// deduplicate branches.
    fn compile_pass1(&self, state: &mut OpCompile);

    /// Second compile pass, used to actually compile both the
    /// immediates and bytecode. Returns the resulting slot + npw2.
    fn compile_pass2(&self, state: &mut OpCompile) -> (u8, u16);
}


// schedule branches in operations in order to minimize slot usage, note this
// macro is only designed for compile_pass2 and if I could put the macro in
// a different scope I would
//
// we don't know the actual slot usage until compilation, so instead we use the
// saturated depth as a heuristic, most of the branches with registers we can save
// are quite small anyways
//
#[cfg(feature="opt-schedule-slots")]
macro_rules! schedule {
    (
        let ($a_npw2:ident, $a_slot:ident) = $a:ident.compile_pass2($a_state:ident);
        let ($b_npw2:ident, $b_slot:ident) = $b:ident.compile_pass2($b_state:ident);
    ) => {
        let a_tuple;
        let b_tuple;
        if $a.depth() > $b.depth() {
            a_tuple = $a.compile_pass2($a_state);
            b_tuple = $b.compile_pass2($b_state);
        } else {
            b_tuple = $b.compile_pass2($b_state);
            a_tuple = $a.compile_pass2($a_state);
        }
        let ($a_npw2, $a_slot) = a_tuple;
        let ($b_npw2, $b_slot) = b_tuple;
    };
    (
        let ($p_npw2:ident, $p_slot:ident) = $p:ident.compile_pass2($p_state:ident);
        let ($a_npw2:ident, $a_slot:ident) = $a:ident.compile_pass2($a_state:ident);
        let ($b_npw2:ident, $b_slot:ident) = $b:ident.compile_pass2($b_state:ident);
    ) => {
        // this isn't perfect, but more efficient than fully sorting
        let a_tuple;
        let b_tuple;
        if $a.depth() > $b.depth() {
            a_tuple = $a.compile_pass2($a_state);
            b_tuple = $b.compile_pass2($b_state);
        } else {
            b_tuple = $b.compile_pass2($b_state);
            a_tuple = $a.compile_pass2($a_state);
        }
        let ($a_npw2, $a_slot) = a_tuple;
        let ($b_npw2, $b_slot) = b_tuple;
        // we're guessing predicates are usually more short lived
        let ($p_npw2, $p_slot) = $p.compile_pass2($p_state);
    };
}
#[cfg(not(feature="opt-schedule-slots"))]
macro_rules! schedule {
    (
        let ($a_npw2:ident, $a_slot:ident) = $a:ident.compile_pass2($a_state:ident);
        let ($b_npw2:ident, $b_slot:ident) = $b:ident.compile_pass2($b_state:ident);
    ) => {
        let ($a_npw2, $a_slot) = $a.compile_pass2($a_state);
        let ($b_npw2, $b_slot) = $b.compile_pass2($b_state);
    };
    (
        let ($p_npw2:ident, $p_slot:ident) = $p:ident.compile_pass2($p_state:ident);
        let ($a_npw2:ident, $a_slot:ident) = $a:ident.compile_pass2($a_state:ident);
        let ($b_npw2:ident, $b_slot:ident) = $b:ident.compile_pass2($b_state:ident);
    ) => {
        let ($a_npw2, $a_slot) = $a.compile_pass2($a_state);
        let ($b_npw2, $b_slot) = $b.compile_pass2($b_state);
        // we're guessing predicates are usually more short lived
        let ($p_npw2, $p_slot) = $p.compile_pass2($p_state);
    };
}

impl<T: OpU> DynOpNode for OpNode<T> {
    fn npw2(&self) -> u8 {
        T::NPW2
    }

    fn flags(&self) -> u8 {
        self.flags
    }

    fn depth(&self) -> u32 {
        #[cfg(feature="opt-schedule-slots")]
        {
            self.depth
        }
        #[cfg(not(feature="opt-schedule-slots"))]
        {
            0
        }
    }

    fn is_imm(&self) -> bool {
        match self.kind {
            OpKind::Const(_) => true,
            OpKind::Imm(_) => true,
            _ => false,
        }
    }

    fn is_sym(&self) -> bool {
        self.flags & Self::SYM == Self::SYM
    }

    fn is_const(&self) -> bool {
        self.flags & Self::SECRET != Self::SECRET
    }

    fn is_const_zero(&self) -> bool {
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_zero(),
            _                        => false,
        }
    }

    fn is_const_one(&self) -> bool {
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_one(),
            _                        => false,
        }
    }

    fn is_const_ones(&self) -> bool {
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_ones(),
            _                        => false,
        }
    }

    fn is_const_u16(&self, lnpw2: Option<u8>) -> bool {
        self.get_const_u16(lnpw2).is_some()
    }

    fn get_const_u16(&self, lnpw2: Option<u8>) -> Option<(u8, u16)> {
        match (self.is_const(), &self.kind, lnpw2) {
            (true, OpKind::Const(v), Some(lnpw2)) => {
                if v.is_extend_splat(0, T::NPW2-lnpw2) {
                    Some((lnpw2, i16::from(v.to_le_bytes().as_ref()[0] as i8) as u16))
                } else if v.is_extend_splat(1, T::NPW2-lnpw2) {
                    Some((lnpw2, u16::from_le_bytes(
                        <_>::try_from(&v.to_le_bytes().as_ref()[..2]).unwrap()
                    )))
                } else {
                    None
                }
            }
            (true, OpKind::Const(v), None) => {
                for lnpw2 in (0..=T::NPW2).rev() {
                    if v.is_extend_splat(0, T::NPW2-lnpw2) {
                        return Some((lnpw2, i16::from(v.to_le_bytes().as_ref()[0] as i8) as u16));
                    } else if v.is_extend_splat(1, T::NPW2-lnpw2) {
                        return Some((lnpw2, u16::from_le_bytes(
                            <_>::try_from(&v.to_le_bytes().as_ref()[..2]).unwrap()
                        )));
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn get_const_ne_bytes<'a>(&'a self) -> Option<&'a [u8]> {
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => Some(v.as_ne_bytes()),
            _                        => None,
        }
    }

    fn inc_refs(&self) -> u32 {
        let refs = self.refs.get() + 1;
        self.refs.set(refs);
        refs
    }

    fn dec_refs(&self) -> u32 {
        let refs = self.refs.get() - 1;
        self.refs.set(refs);
        refs
    }

    fn disas_pass1(&self) {
        // mark node as seen
        let refs = self.inc_refs();
        if refs > 1 {
            // already visited?
            return;
        }

        match &self.kind {
            OpKind::Const(_) => {},
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Extract(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Replace(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Select(_, p, a, b) => {
                p.borrow().disas_pass1();
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.borrow().disas_pass1();
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }

            OpKind::ExtendU(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::ExtendS(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Truncate(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Splat(a) => {
                a.borrow().disas_pass1();
            }

            OpKind::Eq(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Ne(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::LtU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::LtS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::GtU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::GtS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::LeU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::LeS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::GeU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::GeS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::MinU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::MinS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::MaxU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::MaxS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }

            OpKind::Neg(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Abs(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Not(a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Clz(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Ctz(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Popcnt(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Add(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Sub(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Mul(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::And(a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Andnot(a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Or(a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Xor(a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Shl(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::ShrU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::ShrS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Rotl(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Rotr(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
        }
    }

    fn disas_pass2(
        &self,
        names: &mut HashMap<usize, String>,
        arbitrary_names: &mut dyn Iterator<Item=String>,
        stmts: &mut dyn io::Write,
    ) -> Result<String, io::Error> {
        // is node shared?
        let refs = self.dec_refs();

        // already computed?
        let name = names.get(&((self as *const _) as usize));
        if let Some(name) = name {
            return Ok(name.clone());
        }

        let expr = match &self.kind {
            OpKind::Const(v) => format!("({}.const {:x})",
                prefix(T::NPW2, 0),
                v
            ),
            OpKind::Imm(v) => format!("({}.imm {:x})",
                prefix(T::NPW2, 0),
                v
            ),
            OpKind::Sym(s) => format!("({}.sym {:?})",
                prefix(T::NPW2, 0),
                s
            ),

            OpKind::Extract(x, a) => format!("({}.extract {} {})",
                prefix(a.borrow().npw2(), a.borrow().npw2()-T::NPW2),
                x,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Replace(x, a, b) => format!("({}.replace {} {} {})",
                prefix(T::NPW2, T::NPW2-b.borrow().npw2()),
                x,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Select(lnpw2, p, a, b) => format!("({}.select {} {} {})",
                prefix(T::NPW2, *lnpw2),
                p.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Shuffle(lnpw2, p, a, b) => format!("({}.shuffle {} {} {})",
                prefix(T::NPW2, *lnpw2),
                p.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind::ExtendU(lnpw2, a) => format!("({}.extend_u {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::ExtendS(lnpw2, a) => format!("({}.extend_s {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Truncate(lnpw2, a) => format!("({}.truncate {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Splat(a) => format!("({}.splat {})",
                prefix(T::NPW2, T::NPW2-a.borrow().npw2()),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind::Eq(lnpw2, a, b) => format!("({}.eq {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Ne(lnpw2, a, b) => format!("({}.ne {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::LtU(lnpw2, a, b) => format!("({}.lt_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LtS(lnpw2, a, b) => format!("({}.lt_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GtU(lnpw2, a, b) => format!("({}.gt_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GtS(lnpw2, a, b) => format!("({}.gt_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LeU(lnpw2, a, b) => format!("({}.le_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LeS(lnpw2, a, b) => format!("({}.le_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GeU(lnpw2, a, b) => format!("({}.ge_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GeS(lnpw2, a, b) => format!("({}.ge_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MinU(lnpw2, a, b) => format!("({}.min_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MinS(lnpw2, a, b) => format!("({}.min_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MaxU(lnpw2, a, b) => format!("({}.max_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MaxS(lnpw2, a, b) => format!("({}.max_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),

            OpKind::Neg(lnpw2, a) => format!("({}.neg {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Abs(lnpw2, a) => format!("({}.abs {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Not(a) => format!("({}.not {})",
                8 << T::NPW2,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Clz(lnpw2, a) => format!("({}.clz {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Ctz(lnpw2, a) => format!("({}.ctz {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Popcnt(lnpw2, a) => format!("({}.popcnt {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Add(lnpw2, a, b) => format!("({}.add {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Sub(lnpw2, a, b) => format!("({}.sub {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Mul(lnpw2, a, b) => format!("({}.mul {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::And(a, b) => format!("({}.and {} {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Andnot(a, b) => format!("({}.andnot {} {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Or(a, b) => format!("({}.or {} {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Xor(a, b) => format!("({}.xor {} {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Shl(lnpw2, a, b) => format!("({}.shl {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::ShrU(lnpw2, a, b) => format!("({}.shr_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::ShrS(lnpw2, a, b) => format!("({}.shr_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rotl(lnpw2, a, b) => format!("({}.rotl {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rotr(lnpw2, a, b) => format!("({}.rotr {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
        };

        // used later? save as stmt?
        if refs > 0 {
            let name = arbitrary_names.next().unwrap();
            names.insert((self as *const _) as usize, name.clone());
            write!(stmts, "    {} = {}\n", name, expr)?;
            Ok(name)
        } else {
            Ok(expr)
        }
    }

    #[cfg(feature="debug-check-refs")]
    fn check_refs(&self) {
        // refs must equal 0 between multi-pass traversals
        assert_eq!(self.refs.get(), 0);

        match &self.kind {
            OpKind::Const(_) => {},
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Extract(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Replace(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Select(_, p, a, b) => {
                p.borrow().check_refs();
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.borrow().check_refs();
                a.borrow().check_refs();
                b.borrow().check_refs();
            }

            OpKind::ExtendU(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::ExtendS(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Truncate(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Splat(a) => {
                a.borrow().check_refs();
            }

            OpKind::Eq(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Ne(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::LtU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::LtS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::GtU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::GtS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::LeU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::LeS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::GeU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::GeS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::MinU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::MinS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::MaxU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::MaxS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }

            OpKind::Neg(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Abs(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Not(a) => {
                a.borrow().check_refs();
            }
            OpKind::Clz(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Ctz(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Popcnt(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Add(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Sub(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Mul(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::And(a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Andnot(a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Or(a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Xor(a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Shl(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::ShrU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::ShrS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Rotl(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Rotr(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
        }
    }


    #[cfg(feature="opt-fold-consts")]
    fn fold_consts(
        &self,
        #[allow(unused)] rc: &Rc<dyn DynOpNode>,
        #[allow(unused)] mut const_pool: Option<&mut ConstPool>
    ) -> Option<Rc<dyn DynOpNode>> {
        // already folded?
        if self.folded.get() {
            return None;
        }
        self.folded.set(true);

        if self.is_const() && !self.is_imm() {
            // oh hey, we're const
            //
            // note this recursively triggers another compilation
            // + execution, so be careful
            //
            // if this fails we just bail on the const folding so the error
            // can be reported at runtime
            if let Ok(v) = self.try_eval() {
                // check for duplicate consts?
                #[cfg(feature="opt-deduplicate-consts")]
                if let Some(const_pool) = const_pool {
                    return Some(const_pool.deduplicate_new(v));
                }

                return Some(Rc::new(Self::new(
                    OpKind::Const(v), 0, 0
                )));
            }
        }

        match &self.kind {
            OpKind::Const(_) => {
                // check for duplicate consts?
                #[cfg(feature="opt-deduplicate-consts")]
                if let Some(const_pool) = const_pool {
                    return const_pool.deduplicate(&rc);
                }
            },

            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Extract(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = x);
            }
            OpKind::Replace(_, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = x);
            }
            OpKind::Select(_, p, a, b) => {
                let mut p = p.borrow_mut(); let p_dyn: Rc<dyn DynOpNode> = p.clone();
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                p.fold_consts(&p_dyn, const_pool.reborrow()).map(|x| *p = Self::dyn_downcast(x));
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::Shuffle(_, p, a, b) => {
                let mut p = p.borrow_mut(); let p_dyn: Rc<dyn DynOpNode> = p.clone();
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                p.fold_consts(&p_dyn, const_pool.reborrow()).map(|x| *p = Self::dyn_downcast(x));
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
            }

            OpKind::ExtendU(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = x);
            }
            OpKind::ExtendS(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = x);
            }
            OpKind::Truncate(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = x);
            }
            OpKind::Splat(a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = x);
            }

            OpKind::Eq(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Eq(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::Ne(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Ne(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::LtU(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::GtU(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::LtS(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::GtS(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::GtU(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::LtU(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::GtS(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::LtS(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::LeU(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::GeU(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::LeS(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::GeS(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::GeU(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::LeU(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::GeS(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::LeS(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::MinU(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::MinU(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::MinS(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::MinS(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::MaxU(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::MaxU(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::MaxS(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::MaxS(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }

            OpKind::Neg(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Abs(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Not(a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                // not has the most powerful set of reductions, fortunately
                // it is a bit unique in this regard
                #[cfg(feature="opt-simple-reductions")]
                match &a.kind {
                    OpKind::Not(a) => {
                        return Some(a.borrow().clone())
                    }
                    OpKind::Eq(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Ne(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::Ne(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Eq(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::LtU(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::GeU(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::LtS(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::GeS(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::GtU(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::LeU(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::GtS(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::LeS(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::LeU(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::GtU(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::LeS(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::GtS(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::GeU(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::LtU(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::GeS(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::LtS(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Clz(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Ctz(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Popcnt(_, a) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Add(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    return Some(b.clone());
                } else if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (OpKind::Neg(y, a), _) if y == x => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Sub(*x,
                                RefCell::new(b.clone()),
                                RefCell::new(a.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    (_, OpKind::Neg(y, b)) if y == x => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Sub(*x,
                                RefCell::new(a.clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Add(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::Sub(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (_, OpKind::Neg(y, b)) if y == x => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Add(*x,
                                RefCell::new(a.clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Mul(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && a.is_const_one() {
                    return Some(b.clone());
                } else if *x == 0 && b.is_const_one() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Mul(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::And(a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_ones() {
                    return Some(b.clone());
                } else if b.is_const_ones() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (OpKind::Not(a), OpKind::Not(b)) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Not(
                                RefCell::new(Rc::new(OpNode::new(
                                    OpKind::Or(
                                        RefCell::new(a.borrow().clone()),
                                        RefCell::new(b.borrow().clone())
                                    ), self.flags, self.depth
                                )))
                            ), self.flags, self.depth
                        )));
                    }
                    (OpKind::Not(a), _) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Andnot(
                                RefCell::new(b.clone()),
                                RefCell::new(a.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    (_, OpKind::Not(b)) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Andnot(
                                RefCell::new(a.clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(None) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::And(
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::Andnot(a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_ones() {
                    return Some(b.clone());
                } else if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (_, OpKind::Not(b)) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::And(
                                RefCell::new(a.clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Or(a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    return Some(b.clone());
                } else if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (OpKind::Not(a), OpKind::Not(b)) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Not(
                                RefCell::new(Rc::new(OpNode::new(
                                    OpKind::And(
                                        RefCell::new(a.borrow().clone()),
                                        RefCell::new(b.borrow().clone())
                                    ), self.flags, self.depth
                                )))
                            ), self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(None) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Or(
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::Xor(a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    return Some(b.clone());
                } else if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(None) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Xor(
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::Shl(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Shl(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::ShrU(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::ShrU(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::ShrS(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::ShrS(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::Rotl(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Rotl(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
            OpKind::Rotr(x, a, b) => {
                let mut a = a.borrow_mut(); let a_dyn: Rc<dyn DynOpNode> = a.clone();
                let mut b = b.borrow_mut(); let b_dyn: Rc<dyn DynOpNode> = b.clone();
                a.fold_consts(&a_dyn, const_pool.reborrow()).map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts(&b_dyn, const_pool.reborrow()).map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-compress-consts")]
                if a.is_const_u16(Some(*x)) {
                    return Some(Rc::new(OpNode::new(
                        OpKind::Rotr(*x,
                            RefCell::new(b.clone()),
                            RefCell::new(a.clone())
                        ),
                        self.flags, self.depth
                    )));
                }
            }
        }

        None
    }

    fn compile_pass1(&self, state: &mut OpCompile) {
        // mark node as seen
        let refs = self.inc_refs();
        if refs > 1 {
            // already visited?
            return;
        }

        // make sure slots left over from previous calculation are reset
        self.slot.set(None);

        match &self.kind {
            OpKind::Const(_) => {
                // handle consts later
            }
            OpKind::Imm(v) => {
                // allocate slot
                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                self.slot.set(Some(slot));

                // write imm to slots
                if state.state.len() < (usize::from(slot)+1) << T::NPW2 {
                    state.state.resize((usize::from(slot)+1) << T::NPW2, 0);
                }

                state.state[
                    usize::from(slot) << T::NPW2
                        .. (usize::from(slot)+1) << T::NPW2
                ].copy_from_slice(v.to_le_bytes().as_ref());

                // initialize arg in bytecode
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Arg, slot, slot, 0
                )));
            }
            OpKind::Sym(_) => {
                assert!(!self.is_const());

                // allocate slot
                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                self.slot.set(Some(slot));

                if state.state.len() < (usize::from(slot)+1) << T::NPW2 {
                    state.state.resize((usize::from(slot)+1) << T::NPW2, 0);
                }

                // we'll fill this in later, use an arbitrary constant
                // to hopefully help debugging
                state.state[
                    usize::from(slot) << T::NPW2
                        .. (usize::from(slot)+1) << T::NPW2
                ].fill(0xcc);

                // initialize arg in bytecode
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Arg, slot, slot, 0
                )));
            }

            OpKind::Extract(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Replace(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Select(_, p, a, b) => {
                p.borrow().compile_pass1(state);
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.borrow().compile_pass1(state);
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }

            OpKind::ExtendU(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::ExtendS(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Truncate(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Splat(a) => {
                a.borrow().compile_pass1(state);
            }

            OpKind::Eq(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Ne(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::LtU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::LtS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::GtU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::GtS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::LeU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::LeS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::GeU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::GeS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::MinU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::MinS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::MaxU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::MaxS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }

            OpKind::Neg(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Abs(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Not(a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Clz(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Ctz(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Popcnt(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Add(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Sub(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Mul(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::And(a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Andnot(a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Or(a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Xor(a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Shl(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::ShrU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::ShrS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Rotl(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Rotr(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
        }
    }

    fn compile_pass2(&self, state: &mut OpCompile) -> (u8, u16) {
        // already computed?
        if let Some(slot) = self.slot.get() {
            return (T::NPW2, slot);
        }

        match &self.kind {
            OpKind::Const(v) => {
                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                #[allow(unused_mut, unused_assignments)] let mut extend_npw2 = T::NPW2;
                #[allow(unused_mut, unused_assignments)] let mut splat_npw2 = T::NPW2;

                // can we use a smaller encoding?
                #[cfg(feature="opt-compress-consts")]
                {
                    let extend_splat = v.find_extend_splat();
                    extend_npw2 = extend_splat.0;
                    splat_npw2 = extend_splat.1;
                }

                // fall back to uncompressed encodings
                if extend_npw2 <= 2 {
                    // fits in a splat_const (32-bit immediate)
                    let mut buf = Vec::from(v.to_le_bytes().as_ref());
                    buf.truncate(1 << extend_npw2);
                    buf.resize(4, if buf[buf.len()-1] & 0x80 == 0x80 { 0xff } else { 0x00 });

                    state.bytecode.push(u64::from(OpIns::with_ab(
                        T::NPW2, T::NPW2-splat_npw2, OpCode::SplatC, slot,
                        u32::from_le_bytes(<_>::try_from(&buf[..]).unwrap())
                    )));
                } else {
                    // does not fit, just follows in instruction stream
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, T::NPW2-splat_npw2, OpCode::SplatLongC, slot,
                        0, u16::from(extend_npw2), 
                    )));

                    let mut buf = Vec::from(v.to_le_bytes().as_ref());
                    buf.truncate(1 << extend_npw2);
                    for i in (0..buf.len()).step_by(8) {
                        state.bytecode.push(
                            u64::from_le_bytes(<_>::try_from(&buf[i..i+8]).unwrap())
                        );
                    }
                }

                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Imm(_) => {
                // should be entirely handled in first pass
                unreachable!()
            }
            OpKind::Sym(_) => {
                // should be entirely handled in first pass
                unreachable!()
            }

            OpKind::Select(lnpw2, p, a, b) => {
                let p = p.borrow();
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (p_npw2, p_slot) = p.compile_pass2(state);
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let p_refs = p.dec_refs();
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if p_refs == 0 {
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Select, p_slot, a_slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }
                    self.slot.set(Some(p_slot));
                    (T::NPW2, p_slot)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, 0, OpCode::Splat, slot, p_slot, 0
                    )));
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Select, slot, a_slot, b_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_npw2, p_slot); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }
                    self.slot.set(Some(slot));
                    (T::NPW2, slot)
                }
            }
            OpKind::Shuffle(lnpw2, p, a, b) => {
                let p = p.borrow();
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (p_npw2, p_slot) = p.compile_pass2(state);
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let p_refs = p.dec_refs();
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if p_refs == 0 {
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Shuffle, p_slot, a_slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }
                    self.slot.set(Some(p_slot));
                    (T::NPW2, p_slot)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, 0, OpCode::Splat, slot, p_slot, 0
                    )));
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Shuffle, slot, a_slot, b_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_npw2, p_slot); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }
                    self.slot.set(Some(slot));
                    (T::NPW2, slot)
                }
            }
            OpKind::Extract(lane, a) => {
                let a = a.borrow();
                assert!(T::NPW2 <= a.npw2());
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    a_npw2, a_npw2-T::NPW2, OpCode::Extract, slot, a_slot, *lane
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Replace(lane, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                assert!(T::NPW2 >= b.npw2());
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, T::NPW2-b_npw2, OpCode::Replace, a_slot, b_slot, *lane
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }
                    self.slot.set(Some(a_slot));
                    (T::NPW2, a_slot)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, 0, OpCode::Splat, slot, a_slot, 0
                    )));
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, T::NPW2-b_npw2, OpCode::Replace, slot, b_slot, *lane
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }
                    self.slot.set(Some(slot));
                    (T::NPW2, slot)
                }
            }

            OpKind::ExtendU(lnpw2, a) => {
                let a = a.borrow();
                assert!(T::NPW2 >= a.npw2());
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::ExtendU, slot, a_slot, u16::from(*lnpw2)
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::ExtendS(lnpw2, a) => {
                let a = a.borrow();
                assert!(T::NPW2 >= a.npw2());
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::ExtendS, slot, a_slot, u16::from(*lnpw2)
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Truncate(lnpw2, a) => {
                let a = a.borrow();
                assert!(T::NPW2 <= a.npw2());
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    a_npw2, a_npw2-T::NPW2, OpCode::Truncate, slot, a_slot, u16::from(*lnpw2)
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Splat(a) => {
                let a = a.borrow();
                assert!(T::NPW2 >= a.npw2());
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::Splat, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }

            #[cfg(feature="opt-compress-consts")]
            OpKind::Eq(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::EqC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Eq(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Eq, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Ne(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::NeC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Ne(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Ne, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::LtU(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LtUC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::LtU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LtU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::LtS(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LtSC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::LtS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LtS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::GtU(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GtUC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::GtU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GtU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::GtS(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GtSC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::GtS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GtS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::LeU(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LeUC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::LeU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LeU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::LeS(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LeSC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::LeS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LeS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::GeU(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GeUC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::GeU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GeU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::GeS(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GeSC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::GeS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GeS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::MinU(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MinUC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::MinU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MinU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::MinS(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MinSC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::MinS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MinS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::MaxU(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MaxUC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::MaxU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MaxU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::MaxS(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MaxSC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::MaxS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MaxS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Neg(lnpw2, a) => {
                let a = a.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Neg, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Abs(lnpw2, a) => {
                let a = a.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Abs, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Not(a) => {
                let a = a.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Not, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Clz(lnpw2, a) => {
                let a = a.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Clz, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Ctz(lnpw2, a) => {
                let a = a.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Ctz, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Popcnt(lnpw2, a) => {
                let a = a.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Popcnt, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Add(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::AddC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Add(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Add, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Sub(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::SubC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Sub(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Sub, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Mul(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MulC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Mul(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Mul, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::And(a, b) if b.borrow().is_const_u16(None) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (lnpw2, b_const) = b.get_const_u16(None).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, lnpw2, OpCode::AndC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::And(a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::And, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Andnot(a, b) if b.borrow().is_const_u16(None) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (lnpw2, b_const) = b.get_const_u16(None).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, lnpw2, OpCode::AndnotC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Andnot(a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Andnot, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Or(a, b) if b.borrow().is_const_u16(None) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (lnpw2, b_const) = b.get_const_u16(None).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, lnpw2, OpCode::OrC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Or(a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Or, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Xor(a, b) if b.borrow().is_const_u16(None) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (lnpw2, b_const) = b.get_const_u16(None).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, lnpw2, OpCode::XorC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Xor(a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Xor, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Shl(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::ShlC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Shl(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Shl, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::ShrU(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::ShrUC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::ShrU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::ShrU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::ShrS(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::ShrSC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::ShrS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::ShrS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Rotl(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::RotlC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Rotl(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Rotl, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            #[cfg(feature="opt-compress-consts")]
            OpKind::Rotr(lnpw2, a, b) if b.borrow().is_const_u16(Some(*lnpw2)) => {
                let a = a.borrow();
                let b = b.borrow();
                let (a_npw2, a_slot) = a.compile_pass2(state);
                let (_, b_const) = b.get_const_u16(Some(*lnpw2)).unwrap();
                let a_refs = a.dec_refs();
                b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::RotrC, slot, a_slot, b_const
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
            OpKind::Rotr(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_npw2, a_slot) = a.compile_pass2(state);
                    let (b_npw2, b_slot) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_npw2, a_slot); }
                if b_refs == 0 { state.slot_pool.dealloc(b_npw2, b_slot); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Rotr, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (T::NPW2, slot)
            }
        }
    }
}

