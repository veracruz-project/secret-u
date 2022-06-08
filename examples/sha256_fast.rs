//! SHA256 example
//!
//! Based on implementation from here:
//! https://github.com/B-Con/crypto-algorithms
//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT

use secret_u::*;
use std::convert::TryFrom;

// helper functions and constants
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
];

fn ch(x: SecretU32, y: SecretU32, z: SecretU32) -> SecretU32 {
    (x.clone() & y) ^ ((!x) & z)
}

fn maj(x: SecretU32, y: SecretU32, z: SecretU32) -> SecretU32 {
    (x.clone() & y.clone()) ^ (x & z.clone()) ^ (y & z)
}

fn ep0(x: SecretU32) -> SecretU32 {
    x.clone().rotate_right(SecretU32::const_(2))
        ^ x.clone().rotate_right(SecretU32::const_(13))
        ^ x.rotate_right(SecretU32::const_(22))
}

fn ep1(x: SecretU32) -> SecretU32 {
    x.clone().rotate_right(SecretU32::const_(6))
        ^ x.clone().rotate_right(SecretU32::const_(11))
        ^ x.rotate_right(SecretU32::const_(25))
}

fn sig0(x: SecretU32) -> SecretU32 {
    x.clone().rotate_right(SecretU32::const_(7))
        ^ x.clone().rotate_right(SecretU32::const_(18))
        ^ (x >> SecretU32::const_(3))
}

fn sig1(x: SecretU32) -> SecretU32 {
    x.clone().rotate_right(SecretU32::const_(17))
        ^ x.clone().rotate_right(SecretU32::const_(19))
        ^ (x >> SecretU32::const_(10))
}

// sha256 context
struct Sha256 {
    data: Vec<SecretU8>,
    bitlen: usize,
    state: SecretU32x8,
    transform_lambda: Box<dyn Fn(SecretU32x8, SecretU8x64) -> SecretU32x8>,
}

impl Sha256 {
    fn transform(state: SecretU32x8, data: SecretU8x64) -> SecretU32x8 {
        let m = {
            let mut m: Vec<SecretU32> = Vec::new();
            for i in 0..16 {
                let word = SecretU32x16::from_cast(data.clone()).extract(i);
                m.push(word.reverse_bytes());
            }
            for i in 16..64 {
                m.push(
                    sig1(m[i-2].clone())
                        + m[i-7].clone()
                        + sig0(m[i-15].clone())
                        + m[i-16].clone()
                );
            }
            m
        };

        let mut a = state.clone().extract(0);
        let mut b = state.clone().extract(1);
        let mut c = state.clone().extract(2);
        let mut d = state.clone().extract(3);
        let mut e = state.clone().extract(4);
        let mut f = state.clone().extract(5);
        let mut g = state.clone().extract(6);
        let mut h = state.clone().extract(7);

        for i in 0..64 {
            let t1 = h.clone()
                + ep1(e.clone())
                + ch(e.clone(), f.clone(), g.clone())
                + SecretU32::const_(K[i])
                + m[i].clone();
            let t2 = ep0(a.clone())
                + maj(a.clone(), b.clone(), c.clone());
            h = g.clone();
            g = f.clone();
            f = e.clone();
            e = d.clone() + t1.clone();
            d = c.clone();
            c = b.clone();
            b = a.clone();
            a = t1 + t2;
        }

        state + SecretU32x8::from([a, b, c, d, e, f, g, h])
    }

    pub fn new() -> Sha256 {
        // compile the core transform
        let transform_lambda = compile!(
            |state: SecretU32x8, data: SecretU8x64| -> SecretU32x8 {
                Self::transform(state, data)
            }
        );

        Sha256 {
            data: Vec::with_capacity(64),
            bitlen: 0,
            state: SecretU32x8::from([
                0x6a09e667,
                0xbb67ae85,
                0x3c6ef372,
                0xa54ff53a,
                0x510e527f,
                0x9b05688c,
                0x1f83d9ab,
                0x5be0cd19,
            ]),
            transform_lambda: Box::new(transform_lambda)
        }
    }

    pub fn update(&mut self, data: &[SecretU8]) {
        for b in data {
            self.data.push(b.clone());
            if self.data.len() == 64 {
                self.state = (self.transform_lambda)(
                    self.state.clone(),
                    SecretU8x64::try_from(self.data.clone()).ok().unwrap()
                );
                self.bitlen += 512;
            }
        }
    }

    /// Updates can avoid an extra step of packing data if delivered
    /// in 64-byte chunks
    pub fn update_aligned(&mut self, data: &[SecretU8x64]) {
        assert!(self.data.len() == 0);
        for chunk in data {
            self.state = (self.transform_lambda)(
                self.state.clone(),
                chunk.clone()
            );
            self.bitlen += 512;
        }
    }

    pub fn finalize(&mut self) -> [SecretU8; 32] {
        // Get message bitlen
        let bitlen = self.bitlen + 8*self.data.len();

        // Pad whatever data is left in the buffer
        if self.data.len() < 56 {
            self.data.push(SecretU8::const_(0x80));
            while self.data.len() < 56 {
                self.data.push(SecretU8::zero());
            }
        } else {
            self.data.push(SecretU8::const_(0x80));
            while self.data.len() < 64 {
                self.data.push(SecretU8::zero());
            }
            self.state = (self.transform_lambda)(
                self.state.clone(),
                SecretU8x64::try_from(self.data.clone()).ok().unwrap()
            );
            self.data.clear();
            while self.data.len() < 56 {
                self.data.push(SecretU8::zero());
            }
        }

        // Append to the padding the total message's length in bits and transform
        self.data.push(SecretU8::new((bitlen >> 56) as u8));
        self.data.push(SecretU8::new((bitlen >> 48) as u8));
        self.data.push(SecretU8::new((bitlen >> 40) as u8));
        self.data.push(SecretU8::new((bitlen >> 32) as u8));
        self.data.push(SecretU8::new((bitlen >> 24) as u8));
        self.data.push(SecretU8::new((bitlen >> 16) as u8));
        self.data.push(SecretU8::new((bitlen >>  8) as u8));
        self.data.push(SecretU8::new((bitlen >>  0) as u8));
        self.state = (self.transform_lambda)(
            self.state.clone(),
            SecretU8x64::try_from(self.data.clone()).ok().unwrap()
        );

        // Since this implementation uses little endian byte ordering and SHA uses big endian,
        // reverse all the bytes when copying the final state to the output hash
        let mut hash: [SecretU8; 32] = Default::default();
        for i in 0..4 {
            hash[i+ 0] = SecretU8::from_cast(self.state.clone().extract(0) >> SecretU32::const_(24-8*i as u32));
            hash[i+ 4] = SecretU8::from_cast(self.state.clone().extract(1) >> SecretU32::const_(24-8*i as u32));
            hash[i+ 8] = SecretU8::from_cast(self.state.clone().extract(2) >> SecretU32::const_(24-8*i as u32));
            hash[i+12] = SecretU8::from_cast(self.state.clone().extract(3) >> SecretU32::const_(24-8*i as u32));
            hash[i+16] = SecretU8::from_cast(self.state.clone().extract(4) >> SecretU32::const_(24-8*i as u32));
            hash[i+20] = SecretU8::from_cast(self.state.clone().extract(5) >> SecretU32::const_(24-8*i as u32));
            hash[i+24] = SecretU8::from_cast(self.state.clone().extract(6) >> SecretU32::const_(24-8*i as u32));
            hash[i+28] = SecretU8::from_cast(self.state.clone().extract(7) >> SecretU32::const_(24-8*i as u32));
        }
        hash
    }
}

fn sha256(message: &[SecretU8]) -> [SecretU8; 32] {
    let mut state = Sha256::new();
    state.update(message);
    state.finalize()
}

fn bench(path: &str) -> ! {
    use std::io::Read;

    let mut file = std::fs::File::open(path).unwrap();
    let mut state = Sha256::new();
    loop {
        let mut block = [0; 64];
        let diff = file.read(&mut block).unwrap();
        if diff == 64 {
            state.update_aligned(&[SecretU8x64::from(block)]);
        } else {
            state.update(&block[..diff].into_iter()
                .map(|b| SecretU8::new(*b))
                .collect::<Vec<_>>());
            break;
        }
    }

    let hash = state.finalize();
    let hash = IntoIterator::into_iter(hash)
        .map(|b| b.declassify())
        .collect::<Vec<_>>();

    print!("hash: ");
    for h in hash.iter() {
        print!("{:02x}", h);
    }
    println!();

    std::process::exit(0);
}

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() > 1 {
        bench(&args[1]);
    }

    let data = b"Hello World!";

    let data = data.into_iter()
        .map(|b| SecretU8::new(*b))
        .collect::<Vec<_>>();

    let hash = sha256(&data);

    let hash = IntoIterator::into_iter(hash)
        .map(|b| b.declassify())
        .collect::<Vec<_>>();

    print!("hash: ");
    for h in hash.iter() {
        print!("{:02x}", h);
    }
    println!();
    assert_eq!(
        &hash,
        &b"\x7f\x83\xb1\x65\x7f\xf1\xfc\x53\xb9\x2d\xc1\x81\x48\xa1\xd6\x5d\
           \xfc\x2d\x4b\x1f\xa3\xd6\x77\x28\x4a\xdd\xd2\x00\x12\x6d\x90\x69"
    );
}

