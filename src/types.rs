//! Definitions of secret integers


// separate crate for parallel builds
pub use secret_u_types::types::*;


#[cfg(test)]
mod tests {
    use super::*;
    use crate::traits::*;
    use std::io;

    #[test]
    fn int_bool1() {
        println!();
        let a = SecretBool::new(true);
        let b = SecretBool::new(true);
        let x = (a.clone() & b.clone()).eq(a | b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, true);
    }

    #[test]
    fn int_bool2() {
        println!();
        let a = SecretBool::new(true);
        let b = SecretBool::new(false);
        let x = (a.clone() | b.clone()).select(a, b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, true);
    }

    #[test]
    fn int_eqz() {
        println!();
        let a = SecretU32::new(100);
        let b = SecretU32::new(10);
        let x = !a.clone().gt(b.clone());

        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, false);

        let x = (!a.clone().gt(b.clone())).select(a, b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 10);
    }

    #[test]
    fn int_abs() {
        println!();
        let a = SecretI32::new(-100);
        let x = a.abs();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 100);
    }

    #[test]
    fn int_u32() {
        println!();
        let a = SecretU32::new(3);
        let b = SecretU32::new(4);
        let c = SecretU32::new(5);
        let x = (a.clone()*a + b.clone()*b) - (c.clone()*c);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0);
    }

    #[test]
    fn int_i32() {
        println!();
        let a = SecretI32::new(-3);
        let b = SecretI32::new(-4);
        let c = SecretI32::new(-5);
        let x = (a.clone()*a + b.clone()*b) - (c.clone()*c);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0);
    }

    #[test]
    fn int_ord() {
        println!();

        fn test_ord(a: u32, b: u32, c: u32) {
            let sa = SecretU32::new(a);
            let sb = SecretU32::new(b);
            let sc = SecretU32::new(c);
            let x = sb.clone().lt(sc.clone());
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, b < c);

            let x = sa.clamp(sb, sc);
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, a.clamp(b, c));
        }

        test_ord(0, 1, 3);
        test_ord(2, 1, 3);
        test_ord(4, 1, 3);
    }

    #[test]
    fn int_clz() {
        println!();

        fn test_clz(n: u32) {
            let a = SecretU32::new(n);
            let x = a.clone().leading_zeros();
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.leading_zeros());

            let x = a.clone().is_power_of_two();
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.is_power_of_two());

            let x = a.next_power_of_two();
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.next_power_of_two());
        }

        test_clz(0);
        test_clz(1);
        test_clz(2);
        test_clz(3);
    }

    #[test]
    fn int_reverse() {
        println!();

        let a = SecretU32::new(0x12345678);
        let x = a.clone().reverse_bytes();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x78563412);

        let a = SecretU32::new(0x12345678);
        let x = a.clone().reverse_bits();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x1e6a2c48);

        let a = SecretU16x2::from_cast(SecretU32::new(0x12345678));
        let x = SecretU32::from_cast(a.clone().reverse_lanes());
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x56781234);

        let a = SecretU16x2::from_cast(SecretU32::new(0x12345678));
        let x = SecretU32::from_cast(a.clone().reverse_bytes());
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x34127856);

        let a = SecretU16x2::from_cast(SecretU32::new(0x12345678));
        let x = SecretU32::from_cast(a.clone().reverse_bits());
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x2c481e6a);
    }

    #[test]
    fn int_reduce() {
        println!();

        let a = SecretU8x64::new_lanes([
             0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
            32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
            48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]);
        let x = a.horizontal_max();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 63);

        let a = SecretU32x16::new_lanes([
            0,   1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15]);
        let x = a.horizontal_sum();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 120);
    }

    #[test]
    fn int_any_all_none() {
        println!();

        let a = SecretU8x16::new_lanes([0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15]);
        let b = SecretU8x16::new_lanes([1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 16]);
        let c = SecretU8x16::new_lanes([0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0]);
        let a_mask = a.ne(SecretU8x16::const_splat(0));
        let b_mask = b.ne(SecretU8x16::const_splat(0));
        let c_mask = c.ne(SecretU8x16::const_splat(0));
        let (a_none, a_any, a_all) = (a_mask.clone().none(), a_mask.clone().any(), a_mask.clone().all());
        let (b_none, b_any, b_all) = (b_mask.clone().none(), b_mask.clone().any(), b_mask.clone().all());
        let (c_none, c_any, c_all) = (c_mask.clone().none(), c_mask.clone().any(), c_mask.clone().all());
        let x = SecretM8x16::from_lanes([
            a_none,               a_any,                a_all,                SecretBool::false_(),
            b_none,               b_any,                b_all,                SecretBool::false_(),
            c_none,               c_any,                c_all,                SecretBool::false_(),
            SecretBool::false_(), SecretBool::false_(), SecretBool::false_(), SecretBool::false_(),
        ]);

        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [
            false, true,  false, false,
            false, true,  true,  false,
            true,  false, false, false,
            false, false, false, false,
        ]);
    }

    #[test]
    fn int_lane_casts() {
        println!();

        let a = SecretU32x16::new_lanes([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]);
        let x = SecretU8x16::from_cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]);

        let a = SecretU256x2::from_lanes([
            SecretU256::from(SecretU16::new(1000)),
            SecretU256::from(SecretU16::new(2000))
        ]);
        let x = SecretU16x2::from_cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [1000, 2000]);

        let a = SecretU8x16::new_lanes([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]);
        let x = SecretU32x16::from(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]);

        let a = SecretU16x2::new_lanes([1000, 2000]);
        let b = SecretU256x2::from(a);
        let x = SecretU32x2::from_cast(b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [1000, 2000]);

        let a = SecretI32x16::new_lanes([-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16]);
        let x = SecretI8x16::from_cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16]);

        let a = SecretI256x2::from_lanes([
            SecretI256::from(SecretI16::new(-1000)),
            SecretI256::from(SecretI16::new(-2000))
        ]);
        let x = SecretI16x2::from_cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [-1000, -2000]);

        let a = SecretI8x16::new_lanes([-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16]);
        let x = SecretI32x16::from(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16]);

        let a = SecretI16x2::new_lanes([-1000, -2000]);
        let b = SecretI256x2::from(a);
        let x = SecretI32x2::from_cast(b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, [-1000, -2000]);
    }

    #[cfg(feature="u262144")]
    #[test]
    fn int_really_big_reverse() {
        println!();

        let mut bytes = [0u8; 1024];
        for i in 0..bytes.len() {
            bytes[i] = i as u8;
        }
        let a = SecretU8x1024::new_lanes(bytes);
        let x = a.clone().reverse_lanes();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        let mut bytes = [0u8; 1024];
        for i in 0..bytes.len() {
            bytes[i] = (bytes.len()-1-i) as u8;
        }
        assert_eq!(v, bytes);

        let mut bytes = [0u8; 1024];
        for i in 0..bytes.len() {
            bytes[i] = i as u8;
        }
        let a = SecretU8192::from_le_bytes(bytes);
        let x = a.clone().reverse_bytes();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_le_bytes();
        println!("{:?}", v);
        let mut bytes = [0u8; 1024];
        for i in 0..bytes.len() {
            bytes[i] = (bytes.len()-1-i) as u8;
        }
        assert_eq!(v, bytes);

        let mut bytes = [0u8; 1024];
        for i in (0..bytes.len()).step_by(2) {
            bytes[i+0] = i as u8;
            bytes[i+1] = (i+1) as u8;
        }
        let a = SecretU16x512::from_le_bytes(bytes);
        let x = a.clone().reverse_bytes();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_le_bytes();
        println!("{:?}", v);
        let mut bytes = [0u8; 1024];
        for i in (0..bytes.len()).step_by(2) {
            bytes[i+0] = (i+1) as u8;
            bytes[i+1] = i as u8;
        }
        assert_eq!(v, bytes);

        let mut bytes = [0u8; 1024];
        for i in 0..bytes.len()/4 {
            bytes[i+  0] = 1;
            bytes[i+256] = 2;
            bytes[i+512] = 3;
            bytes[i+768] = 4;
        }
        let a = SecretU4096x2::from_le_bytes(bytes);
        let x = a.clone().reverse_bytes();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_le_bytes();
        println!("{:?}", v);
        let mut bytes = [0u8; 1024];
        for i in 0..bytes.len()/4 {
            bytes[i+  0] = 2;
            bytes[i+256] = 1;
            bytes[i+512] = 4;
            bytes[i+768] = 3;
        }
        assert_eq!(v, bytes);
    }
}

