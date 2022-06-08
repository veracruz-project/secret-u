//! Core lazy-AST and compiler
//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT


// separate crate for parallel builds
pub use secret_u_optree::*;


#[cfg(test)]
mod tests {
    use super::*;
    use std::io;
    use secret_u_opcode::disas;

    #[test]
    fn compile_add() {
        let example = OpTree::add(0,
            OpTree::<U32>::imm(1u32),
            OpTree::<U32>::imm(2u32)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 4);
        assert_eq!(stack.len(), 12);
    }

    #[test]
    fn compile_add_parallel() {
        let example = OpTree::add(2,
            OpTree::<U32>::imm(0x01020304u32),
            OpTree::<U32>::imm(0x0506fffeu32)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 4);
        assert_eq!(stack.len(), 12);
    }

    #[test]
    fn compile_alignment() {
        let example = OpTree::add(0,
            OpTree::<U16>::extend_s(0,
                OpTree::<U8>::imm(2u8)
            ),
            OpTree::<U16>::truncate(0,
                OpTree::<U32>::imm(1u32),
            ),
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 6);
        assert_eq!(stack.len(), 8);
    }

    #[test]
    fn compile_dag() {
        let two = OpTree::<U32>::imm(2u32);
        let a = OpTree::add(0,
            OpTree::<U32>::imm(1u32),
            OpTree::<U32>::imm(2u32)
        );
        let b = OpTree::shr_s(0,
            a.clone(), two.clone()
        );
        let c = OpTree::shl(0,
            a.clone(), two.clone()
        );
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, b, two),
                c,
            ),
            a,
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 10);
        assert_eq!(stack.len(), 16);
    }

    #[test]
    fn compile_pythag() {
        let a = OpTree::<U32>::imm(3u32);
        let b = OpTree::<U32>::imm(4u32);
        let c = OpTree::<U32>::imm(5u32);
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, a.clone(), a),
                OpTree::mul(0, b.clone(), b)
            ),
            OpTree::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 9);
        assert_eq!(stack.len(), 16);
    }

    #[test]
    fn compile_too_many_casts() {
        // this intentionally has an obnoxious amount of casting
        let a = OpTree::<U8>::imm(1u8);
        let b = OpTree::<U16>::imm(1u16);
        let c = OpTree::<U32>::imm(2u32);
        let d = OpTree::<U64>::imm(3u64);
        let e = OpTree::<U128>::imm(5u128);
        let fib_3 = OpTree::add(0,
            OpTree::<U32>::extend_u(0, b.clone()), OpTree::<U32>::extend_u(0, a.clone())
        );
        let fib_4 = OpTree::add(0,
            OpTree::<U64>::extend_u(0, fib_3.clone()), OpTree::<U64>::extend_u(0, b.clone())
        );
        let fib_5 = OpTree::add(0,
            OpTree::<U128>::extend_u(0, fib_4.clone()), OpTree::<U128>::extend_u(0, fib_3.clone())
        );
        let example = OpTree::and(
            OpTree::and(
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_3.clone(), c)),
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_4.clone(), d))
            ),
            OpTree::<U8>::truncate(0, OpTree::eq(0, fib_5.clone(), e))
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 23);
        assert_eq!(stack.len(), 96);
    }

    #[test]
    fn constant_immediates() {
        let a_imm   = OpTree::<U32>::imm(3u32);
        let a_const = OpTree::<U32>::const_(3u32);
        let b = OpTree::<U32>::const_(4u32);
        let c = OpTree::<U32>::const_(5u32);
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, b.clone(), b),
                OpTree::mul(0, a_imm, a_const)
            ),
            OpTree::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 5);
        assert_eq!(stack.len(), 8);
    }

    #[test]
    fn constant_folding() {
        let a = OpTree::<U32>::const_(3u32);
        let b = OpTree::<U32>::const_(4u32);
        let c = OpTree::<U32>::const_(5u32);
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, a.clone(), a),
                OpTree::mul(0, b.clone(), b)
            ),
            OpTree::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 2);
        assert_eq!(stack.len(), 8);
    }

    #[test]
    fn constant_more_folding() {
        // this intentionally has an obnoxious amount of casting
        let a = OpTree::<U8>::const_(1u8);
        let b = OpTree::<U16>::const_(1u16);
        let c = OpTree::<U32>::const_(2u32);
        let d = OpTree::<U64>::const_(3u64);
        let e = OpTree::<U128>::const_(5u128);
        let fib_3 = OpTree::add(0,
            OpTree::<U32>::extend_u(0, b.clone()), OpTree::<U32>::extend_u(0, a.clone())
        );
        let fib_4 = OpTree::add(0,
            OpTree::<U64>::extend_u(0, fib_3.clone()), OpTree::<U64>::extend_u(0, b.clone())
        );
        let fib_5 = OpTree::add(0,
            OpTree::<U128>::extend_u(0, fib_4.clone()), OpTree::<U128>::extend_u(0, fib_3.clone())
        );
        let example = OpTree::and(
            OpTree::and(
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_3.clone(), c)),
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_4.clone(), d))
            ),
            OpTree::<U8>::truncate(0, OpTree::eq(0, fib_5.clone(), e))
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 2);
        assert_eq!(stack.len(), 1);
    }

    #[test]
    fn compile_slot_defragment() {
        let a = OpTree::<U8>::imm(1u8);
        let b = OpTree::<U8>::imm(2u8);
        let c = OpTree::<U8>::imm(3u8);
        let d = OpTree::<U8>::imm(4u8);
        let e = OpTree::<U8>::imm(5u8);
        let f = OpTree::<U8>::imm(6u8);
        let g = OpTree::<U8>::imm(7u8);
        let h = OpTree::<U8>::imm(8u8);
        let big = OpTree::<U32>::extend_u(0, a);
        let i = OpTree::add(0,
            big.clone(),
            OpTree::add(0,
                big.clone(),
                OpTree::add(0,
                    OpTree::<U32>::extend_u(0, b),
                    OpTree::add(0,
                        OpTree::<U32>::extend_u(0, c),
                        OpTree::add(0,
                            OpTree::<U32>::extend_u(0, d),
                            OpTree::add(0,
                                OpTree::<U32>::extend_u(0, e),
                                OpTree::add(0,
                                    OpTree::<U32>::extend_u(0, f),
                                    OpTree::add(0,
                                        OpTree::<U32>::extend_u(0, g),
                                        OpTree::<U32>::extend_u(0, h)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );
        let example = OpTree::add(0, i.clone(), OpTree::add(0, i, big));

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 27);
        #[cfg(feature="opt-schedule-slots")]
        assert_eq!(stack.len(), 16);
        #[cfg(not(feature="opt-schedule-slots"))]
        assert_eq!(stack.len(), 36);
    }

    #[test]
    fn compile_compressed_consts() {
        let a = OpTree::<U128>::imm([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]);
        let b = OpTree::<U128>::const_([1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([0xfd,0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd]);
        let example = OpTree::add(0, a, b);

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 10);
        assert_eq!(stack.len(), 48);
    }
}
