
// this needs to be in separate crate for proc_macros to work,
// this file is mostly just for testing
pub use secret_u_macros::bitslice;


#[cfg(test)]
mod tests {
    use super::*;
    use std::io;
    use std::convert::TryFrom;
    use crate::lambda_compile;

    // hack to allow testing in same crate
    use crate as secret_u;

    #[bitslice]
    const abcd: [u8; 4] = [
        0x3, 0x2, 0x1, 0x0
    ];

    #[test]
    fn bitslice_abcd() {
        use crate::int::*;
        println!();

        let f = lambda_compile!(|x: SecretU8| -> SecretU8 {
            abcd(x)
        });

        print!("  bytecode:");
        for i in (0..f.bytecode().len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&f.bytecode()[i..i+2]).unwrap()
            ));
        }
        println!();
        f.disas(io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..unsafe { f.stack() }.len() {
            print!(" {:02x}", unsafe { f.stack()[i] });
        }
        println!();

        let mut a = Vec::new();
        for i in 0..4 {
            a.push(f.call(i));
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            vec![3, 2, 1, 0]
        );
    }

    #[bitslice]
    const div3: [u8; 8] = [
        1, 0, 0, 1,
        0, 0, 1, 0,
        0, 1, 0, 0,
        1, 0, 0, 1,
    ];

    #[test]
    fn bitslice_div3() {
        use crate::int::*;
        println!();

        let f = lambda_compile!(|x: SecretU8| -> SecretU8 {
            div3(x)
        });

        print!("  bytecode:");
        for i in (0..f.bytecode().len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&f.bytecode()[i..i+2]).unwrap()
            ));
        }
        println!();
        f.disas(io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..unsafe { f.stack() }.len() {
            print!(" {:02x}", unsafe { f.stack()[i] });
        }
        println!();

        let mut a = Vec::new();
        for i in 0..16 {
            a.push(f.call(i));
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            (0..16)
                .map(|i| if i % 3 == 0 { 1 } else { 0 })
                .collect::<Vec<_>>()
        );
    }

    #[bitslice]
    const hello: [u8; 8] = [
        b'H', b'e', b'l', b'l',
        b'o', b' ', b'W', b'o',
        b'r', b'l', b'd', b'!',
    ];

    #[test]
    fn bitslice_hello() {
        use crate::int::*;
        println!();

        let f = lambda_compile!(|x: SecretU8| -> SecretU8 {
            hello(x)
        });

        print!("  bytecode:");
        for i in (0..f.bytecode().len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&f.bytecode()[i..i+2]).unwrap()
            ));
        }
        println!();
        f.disas(io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..unsafe { f.stack() }.len() {
            print!(" {:02x}", unsafe { f.stack()[i] });
        }
        println!();

        let mut a = Vec::new();
        for i in 0..12 {
            a.push(f.call(i));
        }
        println!("{:?}", a);
        assert_eq!(
            a,
            format!("Hello World!").into_bytes()
        );
    }
}
