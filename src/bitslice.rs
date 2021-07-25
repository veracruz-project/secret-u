
// this needs to be in separate crate for proc_macros to work,
// this file is mostly just for testing
pub use secret_u_macros::static_bitslice;


#[cfg(test)]
mod tests {
    use super::*;
    use std::io;
    use crate::compile_object;

    #[static_bitslice]
    const abcd: [u8; 4] = [
        0x3, 0x2, 0x1, 0x0
    ];

    #[test]
    fn bitslice_abcd() {
        use crate::int::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU8 {
            abcd(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..4 {
            a.push(f.call(SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![3, 2, 1, 0]
        );
    }

    #[static_bitslice(index_type="u32")]
    const div3: [bool; 16] = [
        true,  false, false, true,
        false, false, true,  false,
        false, true,  false, false,
        true,  false, false, true,
    ];

    #[test]
    fn bitslice_div3() {
        use crate::int::*;
        println!();

        let f = compile_object!(|x: SecretU32| -> SecretBool {
            div3(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..16 {
            a.push(f.call(SecretU32::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            (0..16)
                .map(|i| i % 3 == 0)
                .collect::<Vec<_>>()
        );
    }

    #[static_bitslice]
    const big: [u32; 2] = [
        0x12345678,
        0x87654321,
    ];

    #[test]
    fn bitslice_big() {
        use crate::int::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU32 {
            big(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..2 {
            a.push(f.call(SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![0x12345678, 0x87654321]
        );
    }

    #[static_bitslice]
    const hello: [u8; 12] = [
        b'H', b'e', b'l', b'l',
        b'o', b' ', b'W', b'o',
        b'r', b'l', b'd', b'!',
    ];

    #[test]
    fn bitslice_hello() {
        use crate::int::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU8 {
            hello(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..12 {
            a.push(f.call(SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            b"Hello World!"
        );
    }

    #[test]
    fn bitslice_multi() {
        use crate::int::*;
        println!();

        println!("hi b");
        let f = compile_object!(|x: SecretU8, y: SecretU8| -> SecretU8 {
            (hello(x) + hello(y)) & SecretU8::const_(0x7f)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..12 {
            a.push(f.call(SecretU8::new(i), SecretU8::new((i+1)%12)).declassify());
        }
        println!("{:?}", String::from_utf8_lossy(&a));
        assert_eq!(
            a,
            b"-QX[\x0fwFa^P\x05i"
        );
    }

    #[static_bitslice(parallel=4)]
    const par: [u8; 4] = [
        0x12, 0x34, 0x56, 0x78
    ];

    #[test]
    fn bitslice_parallel() {
        use crate::int::*;
        println!();

        let f = compile_object!(|a: SecretU8, b: SecretU8, c: SecretU8, d: SecretU8| -> SecretU32 {
            let (a, b, c, d) = par(a, b, c, d);
            // marshall into u32
            (SecretU32::from(a) << SecretU32::const_(24))
                | (SecretU32::from(b) << SecretU32::const_(16))
                | (SecretU32::from(c) << SecretU32::const_(8))
                | (SecretU32::from(d) << SecretU32::const_(0))
        });

        f.disas(io::stdout()).unwrap();

        let a = f.call(
            SecretU8::new(0),
            SecretU8::new(1),
            SecretU8::new(2),
            SecretU8::new(3)
        ).declassify();
        println!("{:?}", a);
        assert_eq!(a, 0x12345678);
    }
}
