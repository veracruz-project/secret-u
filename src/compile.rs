
// used by macros?
pub use paste::paste;
pub use aligned_utils::bytes::AlignedBytes;


/// A macro for wrapping precompiled (or manually compiled?)
/// code into a


/// A macro for compiling parameterized, secret expressions into 
/// bytecode for fast repeated execution, resulting in a SecretClosure
/// instead of callable Fn.
///
/// Due to current limitations in Rust we can't impl Fn and SecretFn
/// simultaneously (or impl Fn at all actually), so the method `call`
/// is provided instead
///
/// `compile!` provides an alternative simpler interface when you only
/// need a `Fn(blah) -> blah`
///
#[macro_export]
macro_rules! compile_object {
    // helper macros
    (@ident $a:ident) => { $a };
    (@ident $_:ident $($a:ident)+) => { compile_object!(@ident $($a)+) };
    (@str $($a:ident)+) => { stringify!(compile_object!(@ident $($a)+)) };
    (@prim $t:ty) => { <$t as SecretType>::PrimType };
    (@tree $t:ty) => { Rc<OpTree<<$t as SecretType>::TreeType>> };

    ($($move:ident)? |$($($a:ident)+: $t:ty),*| -> $r:ty {$($block:tt)*}) => {{
        $crate::compile::paste! {
            use $crate::int::SecretType;
            use $crate::opcode::OpTree;
            use std::rc::Rc;
            use std::io;

            #[derive(Clone)]
            struct SecretClosure {
                // any arguments that may need patching
                $(
                    [<__sym_$($a)+>]: compile_object!(@tree $t),
                )*

                // bytecode and stack
                __bytecode: $crate::compile::AlignedBytes,
                __stack: $crate::compile::AlignedBytes,
            }

            impl SecretClosure {
                fn compile<F>(f: F) -> SecretClosure
                where
                    F: FnOnce($($t),*) -> $r
                {
                    // create symbols
                    $(
                        let [<__sym_$($a)+>] = OpTree::sym(
                            compile_object!(@str $($a)+)
                        );
                    )*

                    // call user function with symbols
                    let v = f(
                        $(
                            <$t>::from_tree([<__sym_$($a)+>].clone())
                        ),*
                    );

                    // compile tree
                    let (bytecode, stack) = v.tree().compile(true);

                    // return closure
                    SecretClosure {
                        $(
                            [<__sym_$($a)+>]: [<__sym_$($a)+>],
                        )*
                        __bytecode: bytecode,
                        __stack: stack,
                    }
                }

                /// Access to the underlying bytecode
                #[allow(dead_code)]
                pub fn bytecode<'a>(&'a self) -> &'a [u8] {
                    &self.__bytecode
                }

                /// Access to the underlying stack, note that this
                /// may contain secrets and unpatched symbols
                #[allow(dead_code)]
                pub fn stack<'a>(&'a self) -> &'a [u8] {
                    &self.__stack
                }

                /// Write dissassembly to output stream
                #[allow(dead_code)]
                pub fn disas<W: io::Write>(&self, out: W) -> Result<(), io::Error> {
                    $crate::opcode::disas(&self.__bytecode, out)
                }

                /// Call underlying bytecode, returning any errors during execution
                #[allow(dead_code)]
                pub fn try_call(
                    &self,
                    $(compile_object!(@ident $($a)+): compile_object!(@prim $t)),*
                ) -> Result<compile_object!(@prim $r), $crate::error::Error> {
                    // clone since we don't watch to patch the common stack
                    let mut stack = self.__stack.clone();

                    // patch arguments
                    $(
                        self.[<__sym_$($a)+>].patch(
                            compile_object!(@ident $($a)+).to_le_bytes(),
                            &mut stack
                        );
                    )*

                    // execute
                    <$r>::try_eval_bytecode(&self.__bytecode, &mut stack)
                }

                /// Call underlying bytecode
                #[allow(dead_code)]
                pub fn call(
                    &self,
                    $(compile_object!(@ident $($a)+): compile_object!(@prim $t)),*
                ) -> compile_object!(@prim $r) {
                    self.try_call($(compile_object!(@ident $($a)+)),*).unwrap()
                }

                /// Call underlying bytecode, returning any errors during execution,
                /// while maintaining secrecy
                #[allow(dead_code)]
                pub fn try_secret_call(
                    &self,
                    $(compile_object!(@ident $($a)+): $t),*
                ) -> Result<$r, $crate::error::Error> {
                    self.try_call(
                        $(
                            compile_object!(@ident $($a)+).declassify()
                        ),*
                    ).map(|r| <$r>::classify(r))
                }

                /// Call underlying bytecode, while maintaining secrecy
                #[allow(dead_code)]
                pub fn secret_call(
                    &self,
                    $(compile_object!(@ident $($a)+): $t),*
                ) -> $r {
                    self.try_secret_call($(compile_object!(@ident $($a)+)),*).unwrap()
                }
            }

            SecretClosure::compile(
                $($move)? |$($($a)+: $t),*| -> $r {
                    $($block)*
                }
            )
        }
    }}
}

/// A macro for compiling parameterized, secret expressions into 
/// bytecode for fast repeated execution
#[macro_export]
macro_rules! compile {
    // helper macros
    (@ident $a:ident) => { $a };
    (@ident $_:ident $($a:ident)+) => { compile!(@ident $($a)+) };
    (@prim $t:ty) => { <$t as SecretType>::PrimType };

    ($($move:ident)? |$($($a:ident)+: $t:ty),*| -> $r:ty {$($block:tt)*}) => {{
        use $crate::int::SecretType;

        // defer to compile_object and wrap in closure
        let object = compile_object!($($move)? |$($($a)+: $t),*| -> $r {$($block)*});

        move |$(compile!(@ident $($a)+): compile!(@prim $t)),*| -> compile!(@prim $r) {
            object.call($(compile!(@ident $($a)+)),*)
        }
    }}
}


#[cfg(test)]
mod tests {
    use crate::int::*;
    use std::io;
    use std::convert::TryFrom;

    #[test]
    fn compile_add() {
        println!();

        let l = compile_object!(|x: SecretU32, y: SecretU32| -> SecretU32 {
            x + y
        });
        print!("  bytecode:");
        for i in (0..l.bytecode().len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&l.bytecode()[i..i+2]).unwrap()
            ));
        }
        println!();
        l.disas(io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..l.stack().len() {
            print!(" {:02x}", l.stack()[i]);
        }
        println!();
        println!("  call:");
        let v = l.call(1, 2);
        println!("{:?}", v);
        assert_eq!(v, 3);

        let l = compile!(|x: SecretU32, y: SecretU32| -> SecretU32 {
            x + y
        });

        let v = l(1, 2);
        println!("{}", v);
        assert_eq!(v, 3);

        let v = l(3, 4);
        println!("{}", v);
        assert_eq!(v, 7);
    }

    #[test]
    fn compile_pythag() {
        println!();

        let l = compile_object!(|x: SecretU32, y: SecretU32, z: SecretU32| -> SecretBool {
            let a = x.clone()*x + y.clone()*y;
            let b = z.clone()*z;
            a.eq(b)
        });
        print!("  bytecode:");
        for i in (0..l.bytecode().len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&l.bytecode()[i..i+2]).unwrap()
            ));
        }
        println!();
        l.disas(io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..l.stack().len() {
            print!(" {:02x}", l.stack()[i]);
        }
        println!();
        println!("  call:");
        let v = l.try_call(3, 4, 5);
        println!("{:?}", v);

        let l = compile!(|x: SecretU32, y: SecretU32, z: SecretU32| -> SecretBool {
            let a = x.clone()*x + y.clone()*y;
            let b = z.clone()*z;
            a.eq(b)
        });

        let v = l(3, 4, 5);
        println!("{}", v);
        assert_eq!(v, true);

        let v = l(6, 7, 8);
        println!("{}", v);
        assert_eq!(v, false);
    }

    #[test]
    fn compile_sqrt() {
        println!();

        // a simple binary-search based sqrt
        let l = compile_object!(|x: SecretU32| -> SecretU32 {
            // binary search
            let mut lo = SecretU32::const_(0);
            let mut hi = x.clone();

            // each round determines one bit, so only need log(x) rounds
            for _ in 0..32 {
                // test mid
                let mid = (lo.clone() + hi.clone()) / SecretU32::const_(2);
                let mid_sq = mid.clone()*mid.clone();

                // find new lo/hi using select to preserve const-time
                let mid_sq_lt = mid_sq.lt(x.clone());
                lo = mid_sq_lt.clone().select(mid.clone(), lo.clone());
                hi = mid_sq_lt.clone().select(hi.clone(), mid.clone());
            }

            // lo and hi should converge
            hi
        });
        print!("  bytecode:");
        for i in (0..l.bytecode().len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&l.bytecode()[i..i+2]).unwrap()
            ));
        }
        println!();
        l.disas(io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..l.stack().len() {
            print!(" {:02x}", l.stack()[i]);
        }
        println!();
        println!("  call:");
        let v = l.try_call(100);
        println!("{:?}", v);
        assert_eq!(v.unwrap(), 10);

        println!("  call:");
        let v = l.try_call(10000);
        println!("{:?}", v);
        assert_eq!(v.unwrap(), 100);
    }
}
