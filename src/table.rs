
// this needs to be in separate crate for proc_macros to work,
// this file is mostly just for testing
pub use secret_u_macros::bitslice_table;
pub use secret_u_macros::shuffle_table;


#[cfg(test)]
mod tests {
    use super::*;
    use std::io;
    use crate::compile_object;

    // bitslice tests

    #[bitslice_table]
    const abcd: [u8; 4] = [
        0x3, 0x2, 0x1, 0x0
    ];

    #[test]
    fn bitslice_abcd() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU8 {
            abcd(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..4 {
            a.push(f.call(&SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![3, 2, 1, 0]
        );
    }

    #[bitslice_table(parallel=4)]
    const par: [u8; 4] = [
        0x12, 0x34, 0x56, 0x78
    ];

    #[test]
    fn bitslice_parallel() {
        use crate::*;
        println!();

        let f = compile_object!(|xs: SecretU8x4| -> SecretU8x4 {
            par(xs)
        });

        f.disas(io::stdout()).unwrap();

        let a = f.call(&SecretU8x4::new_lanes(
            0,
            1,
            2,
            3
        )).declassify_lanes();
        println!("{:?}", a);
        assert_eq!(a, (0x12, 0x34, 0x56, 0x78));
    }

    #[bitslice_table(index_type="u32")]
    const div3: [bool; 16] = [
        true,  false, false, true,
        false, false, true,  false,
        false, true,  false, false,
        true,  false, false, true,
    ];

    #[bitslice_table(index_type="u32", parallel=8)]
    const div3_par: [bool; 16] = [
        true,  false, false, true,
        false, false, true,  false,
        false, true,  false, false,
        true,  false, false, true,
    ];

    #[test]
    fn bitslice_div3() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU32| -> SecretBool {
            div3(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..16 {
            a.push(f.call(&SecretU32::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            (0..16)
                .map(|i| i % 3 == 0)
                .collect::<Vec<_>>()
        );
    }

    #[bitslice_table]
    const big: [u32; 2] = [
        0x12345678,
        0x87654321,
    ];

    #[bitslice_table(parallel=8)]
    const big_bitslice_par: [u32; 2] = [
        0x12345678,
        0x87654321,
    ];

    #[test]
    fn bitslice_big() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU32 {
            big(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..2 {
            a.push(f.call(&SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![0x12345678, 0x87654321]
        );
    }

    #[bitslice_table]
    const hello: [u8; 12] = [
        b'H', b'e', b'l', b'l',
        b'o', b' ', b'W', b'o',
        b'r', b'l', b'd', b'!',
    ];

    #[bitslice_table(parallel=64)]
    const hello_par: [u8; 12] = [
        b'H', b'e', b'l', b'l',
        b'o', b' ', b'W', b'o',
        b'r', b'l', b'd', b'!',
    ];

    #[test]
    fn bitslice_hello() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU8 {
            hello(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..12 {
            a.push(f.call(&SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            b"Hello World!"
        );
    }

    #[test]
    fn bitslice_multi() {
        use crate::*;
        println!();

        println!("hi b");
        let f = compile_object!(|x: SecretU8, y: SecretU8| -> SecretU8 {
            (hello(x) + hello(y)) & SecretU8::const_(0x7f)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..12 {
            a.push(f.call(&SecretU8::new(i), &SecretU8::new((i+1)%12)).declassify());
        }
        println!("{:?}", String::from_utf8_lossy(&a));
        assert_eq!(
            a,
            b"-QX[\x0fwFa^P\x05i"
        );
    }

    #[bitslice_table(parallel=4)]
    const is_prime: [bool; 256] = [
        false, false, true,  true,  false, true,  false, true,
        false, false, false, true,  false, true,  false, false,
        false, true,  false, true,  false, false, false, true,
        false, false, false, false, false, true,  false, true,
        false, false, false, false, false, true,  false, false,
        false, true,  false, true,  false, false, false, true,
        false, false, false, false, false, true,  false, false,
        false, false, false, true,  false, true,  false, false,
        false, false, false, true,  false, false, false, true,
        false, true,  false, false, false, false, false, true,
        false, false, false, true,  false, false, false, false,
        false, true,  false, false, false, false, false, false,
        false, true,  false, false, false, true,  false, true,
        false, false, false, true,  false, true,  false, false,
        false, true,  false, false, false, false, false, false,
        false, false, false, false, false, false, false, true,
        false, false, false, true,  false, false, false, false,
        false, true,  false, true,  false, false, false, false,
        false, false, false, false, false, true,  false, true,
        false, false, false, false, false, true,  false, false,
        false, false, false, true,  false, false, false, true,
        false, false, false, false, false, true,  false, false,
        false, false, false, true,  false, true,  false, false,
        false, false, false, false, false, false, false, true,
        false, true,  false, false, false, true,  false, true,
        false, false, false, false, false, false, false, false,
        false, false, false, true,  false, false, false, false,
        false, false, false, false, false, false, false, true,
        false, false, false, true,  false, true,  false, false,
        false, true,  false, false, false, false, false, true,
        false, true,  false, false, false, false, false, false,
        false, false, false, true,  false, false, false, false
    ];

    #[test]
    fn bitslice_is_prime() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU8x4| -> SecretM8x4 {
            is_prime(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in (0..16).step_by(4) {
            let p = f.call(&SecretU8x4::new_lanes(i, i+1, i+2, i+3)).declassify_lanes();
            if p.0 { a.push(i)   }
            if p.1 { a.push(i+1) }
            if p.2 { a.push(i+2) }
            if p.3 { a.push(i+3) }
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![2,3,5,7,11,13]
        );
    }


    // shuffle tests

    #[shuffle_table]
    const abcd_shuffle: [u8; 4] = [
        0x3, 0x2, 0x1, 0x0
    ];

    #[test]
    fn shuffle_abcd() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU8 {
            abcd_shuffle(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..4 {
            a.push(f.call(&SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![3, 2, 1, 0]
        );
    }

    #[shuffle_table(parallel=4)]
    const par_shuffle: [u8; 4] = [
        0x12, 0x34, 0x56, 0x78
    ];

    #[test]
    fn shuffle_parallel() {
        use crate::*;
        println!();

        let f = compile_object!(|xs: SecretU8x4| -> SecretU8x4 {
            par_shuffle(xs)
        });

        f.disas(io::stdout()).unwrap();

        let a = f.call(&SecretU8x4::new_lanes(
            0,
            1,
            2,
            3
        )).declassify_lanes();
        println!("{:?}", a);
        assert_eq!(a, (0x12, 0x34, 0x56, 0x78));
    }

    #[shuffle_table(index_type="u32")]
    const div3_shuffle: [bool; 16] = [
        true,  false, false, true,
        false, false, true,  false,
        false, true,  false, false,
        true,  false, false, true,
    ];

    #[shuffle_table(index_type="u32", parallel=8)]
    const div3_shuffle_par: [bool; 16] = [
        true,  false, false, true,
        false, false, true,  false,
        false, true,  false, false,
        true,  false, false, true,
    ];

    #[test]
    fn shuffle_div3() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU32| -> SecretBool {
            div3_shuffle(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..16 {
            a.push(f.call(&SecretU32::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            (0..16)
                .map(|i| i % 3 == 0)
                .collect::<Vec<_>>()
        );
    }

    #[shuffle_table]
    const big_shuffle: [u32; 2] = [
        0x12345678,
        0x87654321,
    ];

    #[shuffle_table(parallel=8)]
    const big_shuffle_par: [u32; 2] = [
        0x12345678,
        0x87654321,
    ];

    #[test]
    fn shuffle_big() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU32 {
            big_shuffle(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..2 {
            a.push(f.call(&SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![0x12345678, 0x87654321]
        );
    }

    #[shuffle_table]
    const hello_shuffle: [u8; 12] = [
        b'H', b'e', b'l', b'l',
        b'o', b' ', b'W', b'o',
        b'r', b'l', b'd', b'!',
    ];

    #[shuffle_table(parallel=64)]
    const hello_shuffle_par: [u8; 12] = [
        b'H', b'e', b'l', b'l',
        b'o', b' ', b'W', b'o',
        b'r', b'l', b'd', b'!',
    ];

    #[test]
    fn shuffle_hello() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU8| -> SecretU8 {
            hello_shuffle(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..12 {
            a.push(f.call(&SecretU8::new(i)).declassify());
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            b"Hello World!"
        );
    }

    #[test]
    fn shuffle_multi() {
        use crate::*;
        println!();

        println!("hi b");
        let f = compile_object!(|x: SecretU8, y: SecretU8| -> SecretU8 {
            (hello_shuffle(x) + hello_shuffle(y)) & SecretU8::const_(0x7f)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in 0..12 {
            a.push(f.call(&SecretU8::new(i), &SecretU8::new((i+1)%12)).declassify());
        }
        println!("{:?}", String::from_utf8_lossy(&a));
        assert_eq!(
            a,
            b"-QX[\x0fwFa^P\x05i"
        );
    }

    #[shuffle_table(parallel=4)]
    const is_prime_shuffle: [bool; 256] = [
        false, false, true,  true,  false, true,  false, true,
        false, false, false, true,  false, true,  false, false,
        false, true,  false, true,  false, false, false, true,
        false, false, false, false, false, true,  false, true,
        false, false, false, false, false, true,  false, false,
        false, true,  false, true,  false, false, false, true,
        false, false, false, false, false, true,  false, false,
        false, false, false, true,  false, true,  false, false,
        false, false, false, true,  false, false, false, true,
        false, true,  false, false, false, false, false, true,
        false, false, false, true,  false, false, false, false,
        false, true,  false, false, false, false, false, false,
        false, true,  false, false, false, true,  false, true,
        false, false, false, true,  false, true,  false, false,
        false, true,  false, false, false, false, false, false,
        false, false, false, false, false, false, false, true,
        false, false, false, true,  false, false, false, false,
        false, true,  false, true,  false, false, false, false,
        false, false, false, false, false, true,  false, true,
        false, false, false, false, false, true,  false, false,
        false, false, false, true,  false, false, false, true,
        false, false, false, false, false, true,  false, false,
        false, false, false, true,  false, true,  false, false,
        false, false, false, false, false, false, false, true,
        false, true,  false, false, false, true,  false, true,
        false, false, false, false, false, false, false, false,
        false, false, false, true,  false, false, false, false,
        false, false, false, false, false, false, false, true,
        false, false, false, true,  false, true,  false, false,
        false, true,  false, false, false, false, false, true,
        false, true,  false, false, false, false, false, false,
        false, false, false, true,  false, false, false, false
    ];

    #[test]
    fn shuffle_is_prime() {
        use crate::*;
        println!();

        let f = compile_object!(|x: SecretU8x4| -> SecretM8x4 {
            is_prime_shuffle(x)
        });

        f.disas(io::stdout()).unwrap();

        let mut a = Vec::new();
        for i in (0..16).step_by(4) {
            let p = f.call(&SecretU8x4::new_lanes(i, i+1, i+2, i+3)).declassify_lanes();
            if p.0 { a.push(i)   }
            if p.1 { a.push(i+1) }
            if p.2 { a.push(i+2) }
            if p.3 { a.push(i+3) }
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![2,3,5,7,11,13]
        );
    }
}
