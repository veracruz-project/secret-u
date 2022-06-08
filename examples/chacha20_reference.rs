//! ChaCha20 examples
//!
//! Based on implementation from here:
//! https://cr.yp.to/chacha.html
//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT

use std::convert::TryFrom;


// ChaCha20 context
struct ChaCha20 {
    // state
    state: [u32; 16],

    // current stream
    x: [u8; 64],
    i: usize,
}

impl ChaCha20 {
    pub fn new(key: &[u8], iv: &[u8]) -> Self {
        assert!(key.len() == 32);
        assert!(iv.len() == 8);

        fn word(bytes: &[u8]) -> u32 {
            u32::from_le_bytes(<[u8;4]>::try_from(bytes).unwrap())
        }

        ChaCha20 {
            state: [
                word(b"expa"),      word(b"nd 3"),      word(b"2-by"),      word(b"te k"),
                word(&key[ 0.. 4]), word(&key[ 4.. 8]), word(&key[ 8..12]), word(&key[12..16]),
                word(&key[16..20]), word(&key[20..24]), word(&key[24..28]), word(&key[28..32]),
                word(&[0; 4]),      word(&[0; 4]),      word(&iv[0..4]),    word(&iv[4..8]),
            ],
            x: [0; 64],
            i: 64,
        }
    }

    /// cipher with 20 rounds + mix array
    fn cipher(&self, state: &[u32; 16]) -> [u32; 16] {
        let mut x = state.clone();
        let mut qr = |a: usize, b: usize, c: usize, d: usize| {
            x[a] = x[a].wrapping_add(x[b]); x[d] ^= x[a]; x[d] = x[d].rotate_left(16);
            x[c] = x[c].wrapping_add(x[d]); x[b] ^= x[c]; x[b] = x[b].rotate_left(12);
            x[a] = x[a].wrapping_add(x[b]); x[d] ^= x[a]; x[d] = x[d].rotate_left( 8);
            x[c] = x[c].wrapping_add(x[d]); x[b] ^= x[c]; x[b] = x[b].rotate_left( 7);
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
            x[i] = x[i].wrapping_add(state[i]);
        }

        x
    }

    #[allow(unused)]
    pub fn encrypt(&mut self, data: &mut [u8]) {
        for i in 0..data.len() {
            if self.i == self.x.len() {
                self.i = 0;

                // encrypt state
                let x = self.cipher(&self.state);
                for i in 0..16 {
                    self.x[i*4..(i+1)*4].copy_from_slice(&x[i].to_le_bytes());
                }

                // increment ctr
                let (ctr, overflow) = self.state[12].overflowing_add(1);
                self.state[12] = ctr;
                if overflow {
                    self.state[13] = self.state[13].wrapping_add(1);
                }
            }

            // xor result
            data[i] ^= self.x[self.i];
            self.i += 1;
        }
    }

    #[allow(unused)]
    pub fn decrypt(&mut self, data: &mut [u8]) {
        self.encrypt(data)
    }
}

/// convenience function for encrypting
#[allow(unused)]
fn chacha20_encrypt(key: &[u8], iv: &[u8], data: &mut [u8]) {
    let mut state = ChaCha20::new(key, iv);
    state.encrypt(data);
}

/// convenience function for decrypting
#[allow(unused)]
fn chacha20_decrypt(key: &[u8], iv: &[u8], data: &mut [u8]) {
    // symmetric
    chacha20_encrypt(key, iv, data);
}

fn bench(key: &str, iv: &str, in_path: &str, out_path: &str) -> ! {
    use std::io::Read;
    use std::io::Write;

    let key = std::fs::read(key).unwrap();
    let iv = std::fs::read(iv).unwrap();

    let mut in_file = std::fs::File::open(in_path).unwrap();
    let mut out_file = std::fs::File::create(out_path).unwrap();
    let mut state = ChaCha20::new(&key, &iv);
    loop {
        let mut block = [0; 64];
        let diff = in_file.read(&mut block).unwrap();
        state.encrypt(&mut block);
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
    let mut buf = Vec::from(&IN[..]);
    chacha20_encrypt(&KEY, &IV, &mut buf[..]);

    println!("chacha20 encrypted:");
    print_buf(&buf);
    println!("expected:");
    print_buf(&OUT);
    assert_eq!(buf, OUT);
}
