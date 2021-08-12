//! ChaCha20 examples
//!
//! Based on implementation from here:
//! https://cr.yp.to/chacha.html

use secret_u::*;


// ChaCha20 context
struct ChaCha20 {
    // state
    state: SecretU32x16,

    // current stream
    x: SecretU8x64,
    i: usize,

    // compile bytecode
    compiled_cipher: Option<Box<dyn Fn(&SecretU32x16) -> SecretU8x64>>,
    compiled_inc: Option<Box<dyn Fn(&SecretU32x16) -> SecretU32x16>>,
    compiled_xor: Option<Box<dyn Fn(&SecretU8x64, &SecretU8x64) -> SecretU8x64>>,
}

impl ChaCha20 {
    pub fn new(key: SecretU8x32, iv: SecretU8x8) -> Self {
        let consts = SecretU32x4::const_le_bytes(*b"expand 32-byte k");
        let key = SecretU32x8::from_cast(key);
        let iv = SecretU32x2::from_cast(iv);

        let mut self_ = ChaCha20 {
            state: SecretU32x16::from_lanes(
                consts.clone().extract(0), consts.clone().extract(1), consts.clone().extract(2), consts.clone().extract(3),
                key.clone().extract(0),    key.clone().extract(1),    key.clone().extract(2),    key.clone().extract(3),
                key.clone().extract(4),    key.clone().extract(5),    key.clone().extract(6),    key.clone().extract(7),
                SecretU32::zero(),         SecretU32::zero(),         iv.clone().extract(0),     iv.clone().extract(1),
            ),
            x: SecretU8x64::zero(),
            i: 64,

            compiled_cipher: None,
            compiled_inc: None,
            compiled_xor: None,
        };

        // compile bytecode
        self_.compiled_cipher = Some(Box::new(compile! {
            |x: SecretU32x16| -> SecretU8x64 {
                self_.cipher(x)
            }
        }));

        self_.compiled_inc = Some(Box::new(compile! {
            |x: SecretU32x16| -> SecretU32x16 {
                let x = SecretU64x8::from_cast(x);
                let x = x.clone().replace(6, x.extract(6) + SecretU64::const_(1));
                SecretU32x16::from_cast(x)
            }
        }));

        self_.compiled_xor = Some(Box::new(compile! {
            |x: SecretU8x64, y: SecretU8x64| -> SecretU8x64 {
                x ^ y
            }
        }));

        self_
    }

    /// cipher with 20 rounds + mix array
    fn cipher(&self, state: SecretU32x16) -> SecretU8x64 {
        let state = state.to_vec();
        let mut x = state.iter().cloned().collect::<Vec<_>>();
        let mut qr = |a: usize, b: usize, c: usize, d: usize| {
            x[a] = x[a].clone() + x[b].clone(); x[d] = x[d].clone() ^ x[a].clone(); x[d] = x[d].clone().rotate_left(SecretU32::const_(16));
            x[c] = x[c].clone() + x[d].clone(); x[b] = x[b].clone() ^ x[c].clone(); x[b] = x[b].clone().rotate_left(SecretU32::const_(12));
            x[a] = x[a].clone() + x[b].clone(); x[d] = x[d].clone() ^ x[a].clone(); x[d] = x[d].clone().rotate_left(SecretU32::const_( 8));
            x[c] = x[c].clone() + x[d].clone(); x[b] = x[b].clone() ^ x[c].clone(); x[b] = x[b].clone().rotate_left(SecretU32::const_( 7));
        };

        for _ in (0..20).step_by(2) {
            // odd round
            qr(0, 4,  8, 12);
            qr(1, 5,  9, 13);
            qr(2, 6, 10, 14);
            qr(3, 7, 11, 15);
            // even round
            qr(0, 5, 10, 15);
            qr(1, 6, 11, 12);
            qr(2, 7,  8, 13);
            qr(3, 4,  9, 14);
        }

        // mix array
        for i in 0..16 {
            x[i] += state[i].clone();
        }

        SecretU8x64::from_cast(SecretU32x16::from_slice(&x))
    }

    #[allow(unused)]
    pub fn encrypt_aligned(&mut self, data: &mut [SecretU8x64]) {
        assert!(self.i == 64);

        for i in 0..data.len() {
            // encrypt state
            self.x = (self.compiled_cipher.as_ref().unwrap())(&self.state);

            // increment ctr
            self.state = (self.compiled_inc.as_ref().unwrap())(&self.state);

            // xor result
            data[i] = (self.compiled_xor.as_ref().unwrap())(&data[i], &self.x);
        }
    }

    #[allow(unused)]
    pub fn encrypt(&mut self, data: &mut [SecretU8]) {
        for i in 0..data.len() {
            if self.i == 64 {
                self.i = 0;

                // encrypt state
                self.x = (self.compiled_cipher.as_ref().unwrap())(&self.state);

                // increment ctr
                self.state = (self.compiled_inc.as_ref().unwrap())(&self.state);
            }

            // xor result
            data[i] ^= self.x.clone().extract(self.i);
            self.i += 1;
        }
    }

    #[allow(unused)]
    pub fn decrypt_aligned(&mut self, data: &mut [SecretU8x64]) {
        self.encrypt_aligned(data)
    }

    #[allow(unused)]
    pub fn decrypt(&mut self, data: &mut [SecretU8]) {
        self.encrypt(data)
    }
}

/// convenience function for encrypting
#[allow(unused)]
fn chacha20_encrypt(key: SecretU8x32, iv: SecretU8x8, data: &mut [SecretU8]) {
    let mut state = ChaCha20::new(key, iv);
    state.encrypt(data);
}

/// convenience function for decrypting
#[allow(unused)]
fn chacha20_decrypt(key: SecretU8x32, iv: SecretU8x8, data: &mut [SecretU8]) {
    // symmetric
    chacha20_encrypt(key, iv, data);
}

fn bench(key: &str, iv: &str, in_path: &str, out_path: &str) -> ! {
    use std::io::Read;
    use std::io::Write;

    let key = std::fs::read(key).unwrap();
    let key = SecretU8x32::new_slice(&key);
    let iv = std::fs::read(iv).unwrap();
    let iv = SecretU8x8::new_slice(&iv);

    let mut in_file = std::fs::File::open(in_path).unwrap();
    let mut out_file = std::fs::File::create(out_path).unwrap();
    let mut state = ChaCha20::new(key, iv);
    loop {
        let mut block = [0; 64];
        let diff = in_file.read(&mut block).unwrap();
        if diff == 64 {
            let mut block_s = [SecretU8x64::new_slice(&block)];
            state.encrypt_aligned(&mut block_s);
            block[..].copy_from_slice(&block_s[0].declassify_le_bytes());
        } else {
            let mut block_s = block[..diff].into_iter()
                .map(|b| SecretU8::new(*b))
                .collect::<Vec<_>>();
            state.encrypt(&mut block_s[..]);
            for i in 0..diff {
                block[i] = block_s[i].declassify();
            }
        }
        out_file.write_all(&block[0..diff]).unwrap();
        if diff < 64 {
            break;
        }
    }

    std::process::exit(0);
}

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() > 1 {
        bench(&args[1], &args[2], &args[3], &args[4]);
    }

    // test with test vectors from
    // https://datatracker.ietf.org/doc/html/draft-agl-tls-chacha20poly1305-04#section-7
    const KEY: [u8; 32] = [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    const IV: [u8; 8] = [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    ];
    const IN: [u8; 64] = [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ]; 
    const OUT: [u8; 64] = [
        0x76, 0xb8, 0xe0, 0xad, 0xa0, 0xf1, 0x3d, 0x90, 0x40, 0x5d, 0x6a, 0xe5, 0x53, 0x86, 0xbd, 0x28,
        0xbd, 0xd2, 0x19, 0xb8, 0xa0, 0x8d, 0xed, 0x1a, 0xa8, 0x36, 0xef, 0xcc, 0x8b, 0x77, 0x0d, 0xc7,
        0xda, 0x41, 0x59, 0x7c, 0x51, 0x57, 0x48, 0x8d, 0x77, 0x24, 0xe0, 0x3f, 0xb8, 0xd8, 0x4a, 0x37,
        0x6a, 0x43, 0xb8, 0xf4, 0x15, 0x18, 0xa1, 0x1c, 0xc3, 0x87, 0xb6, 0x69, 0xb2, 0xee, 0x65, 0x86
    ]; 

    fn print_buf(buf: &[u8]) {
        for i in (0..buf.len()).step_by(16) {
            print!("    ");
            for j in 0..16 {
                match buf.get(i+j) {
                    Some(x) => print!("{:02x}", x),
                    None => break,
                }
            }
            println!();
        }
    }

    // test chacha20
    let key = SecretU8x32::new_slice(&KEY);
    let iv = SecretU8x8::new_slice(&IV);
    let mut buf = IN.iter()
        .map(|b| SecretU8::new(*b))
        .collect::<Vec<_>>();
    chacha20_encrypt(key, iv, &mut buf[..]);
    let buf = buf.into_iter()
        .map(|b| b.declassify())
        .collect::<Vec<_>>();

    println!("chacha20 encrypted:");
    print_buf(&buf);
    println!("expected:");
    print_buf(&OUT);
    assert_eq!(buf, OUT);
}
