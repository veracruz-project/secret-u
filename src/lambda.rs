
// used by macros?
pub use paste::paste;
pub use aligned_utils::bytes::AlignedBytes;

// proc_macros provided by secret_u_macros
pub use secret_u_macros::lazy_compile;


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

    (@str $a:ident) => { stringify!($a) };
    (@str $_:ident $($a:ident)+) => { compile_object!(@str $($a)+) };

    ($($move:ident)? |$($($a:ident)+: $t:ty),*| -> $r:ty {$($block:tt)*}) => {{
        $crate::lambda::paste! {
            use $crate::traits::Tree;
            use $crate::optree::OpTree;
            use std::io;
            use std::cell::RefCell;

            #[derive(Clone)]
            struct SecretClosure {
                // any arguments that may need patching
                $(
                    [<__sym_$($a)+>]: <$t as Tree>::Tree,
                )*

                // bytecode, initial state, and working state
                __bytecode: Vec<u64>,
                __init: $crate::lambda::AlignedBytes,
                __state: RefCell<$crate::lambda::AlignedBytes>,
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
                            <$t as Tree>::from_tree([<__sym_$($a)+>].clone())
                        ),*
                    );

                    // compile tree
                    let (bytecode, state) = v.into_tree().compile(true);

                    // working state (copied from init state at runtime
                    let working_state = AlignedBytes::new_zeroed(state.len(), state.align());

                    // return closure
                    SecretClosure {
                        $(
                            [<__sym_$($a)+>]: [<__sym_$($a)+>],
                        )*
                        __bytecode: bytecode,
                        __init: state,
                        __state: RefCell::new(working_state),
                    }
                }

                /// Access to the underlying bytecode
                #[allow(dead_code)]
                pub fn bytecode<'a>(&'a self) -> &'a [u64] {
                    &self.__bytecode
                }

                /// Access to the underlying stack, note that this
                /// may contain secrets and unpatched symbols
                #[allow(dead_code)]
                pub fn state<'a>(&'a self) -> &'a [u8] {
                    &self.__init
                }

                /// Write dissassembly to output stream
                #[allow(dead_code)]
                pub fn disas<W: io::Write>(&self, mut out: W) -> Result<(), io::Error> {
                    write!(out, "stack:")?;
                    for b in self.__init.iter() {
                         write!(out, " {:02x}", b)?;
                    }
                    writeln!(out)?;

                    writeln!(out, "bytecode:")?;
                    $crate::opcode::disas(&self.__bytecode, out)?;
                    Ok(())
                }

                /// Call underlying bytecode, returning any errors during execution
                #[allow(dead_code)]
                pub fn try_call(
                    &self,
                    $(compile_object!(@ident $($a)+): $t),*
                ) -> Result<$r, $crate::error::Error> {
                    // copy since we don't watch to patch the common stack
                    let mut state = self.__state.borrow_mut();
                    state.copy_from_slice(&self.__init);

                    // patch arguments, note we use the tree directly here
                    // since we can assume the underlying bytes are le (users can't)
                    $(
                        self.[<__sym_$($a)+>].patch(
                            &mut state,
                            &compile_object!(@ident $($a)+)
                                .into_tree()
                                .try_eval()?
                                .result()
                        );
                    )*

                    // execute
                    Ok(<$r>::from_tree(OpTree::try_exec(&self.__bytecode, &mut state)?))
                }

                /// Call underlying bytecode
                #[allow(dead_code)]
                pub fn call(
                    &self,
                    $(compile_object!(@ident $($a)+): $t),*
                ) -> $r {
                    self.try_call($(compile_object!(@ident $($a)+)),*).unwrap()
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

    ($($move:ident)? |$($($a:ident)+: $t:ty),*| -> $r:ty {$($block:tt)*}) => {{
        use $crate::compile_object;

        // defer to compile_object and wrap in closure
        let object = compile_object!($($move)? |$($($a)+: $t),*| -> $r {$($block)*});

        move |$(compile!(@ident $($a)+): $t),*| -> $r {
            object.call($(compile!(@ident $($a)+)),*)
        }
    }}
}


#[cfg(test)]
mod tests {
    use crate::*;
    use std::io;

    #[test]
    fn compile_add() {
        println!();

        let l = compile_object!(|x: SecretU32, y: SecretU32| -> SecretU32 {
            x + y
        });
        l.disas(io::stdout()).unwrap();
        println!("call:");
        let v = l.call(SecretU32::new(1), SecretU32::new(2)).declassify();
        println!("{:?}", v);
        assert_eq!(v, 3);

        let l = compile!(|x: SecretU32, y: SecretU32| -> SecretU32 {
            x + y
        });

        let v = l(SecretU32::new(1), SecretU32::new(2)).declassify();
        println!("{}", v);
        assert_eq!(v, 3);

        let v = l(SecretU32::new(3), SecretU32::new(4)).declassify();
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
        l.disas(io::stdout()).unwrap();
        println!("call:");
        let v = l.call(SecretU32::new(3), SecretU32::new(4), SecretU32::new(5)).declassify();
        println!("{:?}", v);

        let l = compile!(|x: SecretU32, y: SecretU32, z: SecretU32| -> SecretBool {
            let a = x.clone()*x + y.clone()*y;
            let b = z.clone()*z;
            a.eq(b)
        });

        let v = l(SecretU32::new(3), SecretU32::new(4), SecretU32::new(5)).declassify();
        println!("{}", v);
        assert_eq!(v, true);

        let v = l(SecretU32::new(6), SecretU32::new(7), SecretU32::new(8)).declassify();
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
                let mid = (lo.clone() + hi.clone()) >> SecretU32::const_(1);
                let mid_sq = mid.clone()*mid.clone();

                // find new lo/hi using select to preserve const-time
                let mid_sq_lt = mid_sq.lt(x.clone());
                lo = mid_sq_lt.clone().select(mid.clone(), lo.clone());
                hi = mid_sq_lt.clone().select(hi.clone(), mid.clone());
            }

            // lo and hi should converge
            hi
        });
        l.disas(io::stdout()).unwrap();
        println!("call:");
        let v = l.call(SecretU32::new(100)).declassify();
        println!("{:?}", v);
        assert_eq!(v, 10);

        println!("  call:");
        let v = l.call(SecretU32::new(10000)).declassify();
        println!("{:?}", v);
        assert_eq!(v, 100);
    }

    #[test]
    #[should_panic(expected = "DeclassifyInCompile")]
    fn compile_declassify_failure() {
        // this should not work, we don't allow declassify because it's
        // probably not what the user intends to do, and not something we
        // actually can compile
        let l = compile!(|x: SecretU32| -> SecretU32 {
            SecretU32::new(x.declassify())
        });

        l(SecretU32::new(123));
    }
}
