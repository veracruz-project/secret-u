
// used by macros?
#[allow(unused)]
use paste::paste;

// match optional mut attribute
macro_rules! __lambda_ident {
    (mut $a:ident) => { $a };
    (    $a:ident) => { $a };
}

// primitive types for each secret type
// TODO can we get this from trait info?
macro_rules! __lambda_prim {
    (SecretBool) => { bool };
    (SecretU8  ) => { u8   };
    (SecretU16 ) => { u16  };
    (SecretU32 ) => { u32  };
    (SecretI8  ) => { i8   };
    (SecretI16 ) => { i16  };
    (SecretI32 ) => { i32  };
}

/// A macro for compiling parameterized, secret expressions into 
/// bytecode for fast repeated execution
#[macro_export]
macro_rules! lambda {
    ($($move:ident)? |$($($a:ident)+: $t:ident),*| -> $ret:ident {$($block:tt)*}) => {{
        fn lambda_compile<F>(f: F)
            -> impl Fn($(__lambda_prim!($t)),*) -> __lambda_prim!($ret)
        where
            F: FnOnce($($t),*) -> $ret
        {
            $crate::lambda::paste! {
                use std::convert::TryInto;

                // create symbols
                $(
                    let [< __sym_ $($a)+ >] = std::rc::Rc::new(
                        $crate::opcode::OpTree::new(
                            $crate::opcode::OpKind::Sym(
                                stringify!(__lambda_ident!($($a)+))
                            )
                        )
                    );
                )*

                // call user function with symbols
                let v = f($(
                    <$t>::from_tree([< __sym_ $($a)+ >].clone())
                ),*);

                // compile tree
                let (bytecode, stack) = v.tree().compile();

                // return function that patches stack based on
                // args and execs the bytecode
                move |$(__lambda_ident!($($a)+): __lambda_prim!($t)),*|
                    -> __lambda_prim!($ret)
                {
                    // clone since we don't watch to patch the common stack
                    let mut stack = stack.clone();

                    // patch arguments
                    $(
                        [< __sym_ $($a)+ >].patch(__lambda_ident!($($a)+), &mut stack);
                    )*

                    let ret = $crate::vm::exec(&bytecode, &mut stack).unwrap();
                    <__lambda_prim!($ret)>::from_le_bytes(ret.try_into().unwrap())
                }
            }
        }

        lambda_compile(
            $($move)? |$($($a)+: $t),*| -> $ret {
                $($block)*
            }
        )
    }}
}


#[cfg(test)]
mod tests {
    use crate::int::*;

    #[test]
    fn lambda_add() {
        println!();

        let l = lambda!(|x: SecretU32, y: SecretU32| -> SecretU32 {
            x + y
        });

        let v = l(1, 2);
        println!("{}", v);
    }
}
