//! SHA256 example
//!
//! Based on implementation from here:
//! https://github.com/B-Con/crypto-algorithms

use secret_u::int::*;

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
    state: [SecretU32; 8],
}

impl Sha256 {
    // TODO we REALLY need to allow tuples from compile statements
    // as it is we can't really compile this
    fn transform(&mut self) {
        debug_assert!(self.data.len() == 64);
        let m = {
            let mut m = Vec::new();
            let mut drain = self.data.drain(..);
            for _ in 0..16 {
                let a = drain.next().unwrap();
                let b = drain.next().unwrap();
                let c = drain.next().unwrap();
                let d = drain.next().unwrap();
                m.push(
                    (SecretU32::from(a) << SecretU32::const_(24))
                        | (SecretU32::from(b) << SecretU32::const_(16))
                        | (SecretU32::from(c) << SecretU32::const_(8))
                        | (SecretU32::from(d) << SecretU32::const_(0))
                );
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

        let mut a = self.state[0].clone();
        let mut b = self.state[1].clone();
        let mut c = self.state[2].clone();
        let mut d = self.state[3].clone();
        let mut e = self.state[4].clone();
        let mut f = self.state[5].clone();
        let mut g = self.state[6].clone();
        let mut h = self.state[7].clone();

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

        // force eval here to keep the internal tree from exploding
        // TODO do we actually need to? it'd be big, but only in bytecode right?
        self.state[0] += a; self.state[0] = self.state[0].clone().eval();
        self.state[1] += b; self.state[1] = self.state[1].clone().eval();
        self.state[2] += c; self.state[2] = self.state[2].clone().eval();
        self.state[3] += d; self.state[3] = self.state[3].clone().eval();
        self.state[4] += e; self.state[4] = self.state[4].clone().eval();
        self.state[5] += f; self.state[5] = self.state[5].clone().eval();
        self.state[6] += g; self.state[6] = self.state[6].clone().eval();
        self.state[7] += h; self.state[7] = self.state[7].clone().eval();
    }

    pub fn new() -> Sha256 {
        Sha256 {
            data: Vec::with_capacity(64),
            bitlen: 0,
            state: [
                SecretU32::const_(0x6a09e667),
                SecretU32::const_(0xbb67ae85),
                SecretU32::const_(0x3c6ef372),
                SecretU32::const_(0xa54ff53a),
                SecretU32::const_(0x510e527f),
                SecretU32::const_(0x9b05688c),
                SecretU32::const_(0x1f83d9ab),
                SecretU32::const_(0x5be0cd19),
            ]
        }
    }

    pub fn update(&mut self, data: &[SecretU8]) {
        for b in data {
            self.data.push(b.clone());
            if self.data.len() == 64 {
                self.transform();
                self.bitlen += 512;
            }
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
            self.transform();
            while self.data.len() < 64 {
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
        self.transform();

        // Since this implementation uses little endian byte ordering and SHA uses big endian,
        // reverse all the bytes when copying the final state to the output hash
        let mut hash: [SecretU8; 32] = Default::default();
        for i in 0..4 {
            hash[i+ 0] = SecretU8::cast(self.state[0].clone() >> SecretU32::const_(24-8*i as u32));
            hash[i+ 4] = SecretU8::cast(self.state[1].clone() >> SecretU32::const_(24-8*i as u32));
            hash[i+ 8] = SecretU8::cast(self.state[2].clone() >> SecretU32::const_(24-8*i as u32));
            hash[i+12] = SecretU8::cast(self.state[3].clone() >> SecretU32::const_(24-8*i as u32));
            hash[i+16] = SecretU8::cast(self.state[4].clone() >> SecretU32::const_(24-8*i as u32));
            hash[i+20] = SecretU8::cast(self.state[5].clone() >> SecretU32::const_(24-8*i as u32));
            hash[i+24] = SecretU8::cast(self.state[6].clone() >> SecretU32::const_(24-8*i as u32));
            hash[i+28] = SecretU8::cast(self.state[7].clone() >> SecretU32::const_(24-8*i as u32));
        }
        hash
    }
}

fn sha256(message: &[SecretU8]) -> [SecretU8; 32] {
    let mut state = Sha256::new();
    state.update(message);
    state.finalize()
}

fn main() {
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
