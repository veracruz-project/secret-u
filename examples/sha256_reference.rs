//! SHA256 example
//!
//! Based on implementation from here:
//! https://github.com/B-Con/crypto-algorithms

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

fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((!x) & z)
}

fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

fn ep0(x: u32) -> u32 {
    x.rotate_right(2)
        ^ x.rotate_right(13)
        ^ x.rotate_right(22)
}

fn ep1(x: u32) -> u32 {
    x.rotate_right(6)
        ^ x.rotate_right(11)
        ^ x.rotate_right(25)
}

fn sig0(x: u32) -> u32 {
    x.rotate_right(7)
        ^ x.rotate_right(18)
        ^ (x >> 3)
}

fn sig1(x: u32) -> u32 {
    x.rotate_right(17)
        ^ x.rotate_right(19)
        ^ (x >> 10)
}

// sha256 context
struct Sha256 {
    data: Vec<u8>,
    bitlen: usize,
    state: [u32; 8],
}

impl Sha256 {
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
                    (u32::from(a) << 24)
                        | (u32::from(b) << 16)
                        | (u32::from(c) << 8)
                        | (u32::from(d) << 0)
                );
            }
            for i in 16..64 {
                m.push(
                    sig1(m[i-2])
                        .wrapping_add(m[i-7])
                        .wrapping_add(sig0(m[i-15]))
                        .wrapping_add(m[i-16])
                );
            }
            m
        };

        let mut a = self.state[0];
        let mut b = self.state[1];
        let mut c = self.state[2];
        let mut d = self.state[3];
        let mut e = self.state[4];
        let mut f = self.state[5];
        let mut g = self.state[6];
        let mut h = self.state[7];

        for i in 0..64 {
            let t1 = h
                .wrapping_add(ep1(e))
                .wrapping_add(ch(e, f, g))
                .wrapping_add(K[i])
                .wrapping_add(m[i]);
            let t2 = ep0(a)
                .wrapping_add(maj(a, b, c));
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }

        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
        self.state[5] = self.state[5].wrapping_add(f);
        self.state[6] = self.state[6].wrapping_add(g);
        self.state[7] = self.state[7].wrapping_add(h);
    }

    pub fn new() -> Sha256 {
        Sha256 {
            data: Vec::with_capacity(64),
            bitlen: 0,
            state: [
                0x6a09e667,
                0xbb67ae85,
                0x3c6ef372,
                0xa54ff53a,
                0x510e527f,
                0x9b05688c,
                0x1f83d9ab,
                0x5be0cd19,
            ]
        }
    }

    pub fn update(&mut self, data: &[u8]) {
        for b in data {
            self.data.push(*b);
            if self.data.len() == 64 {
                self.transform();
                self.bitlen += 512;
            }
        }
    }

    pub fn finalize(&mut self) -> [u8; 32] {
        // Get message bitlen
        let bitlen = self.bitlen + 8*self.data.len();

        // Pad whatever data is left in the buffer
        if self.data.len() < 56 {
            self.data.push(0x80);
            while self.data.len() < 56 {
                self.data.push(0);
            }
        } else {
            self.data.push(0x80);
            while self.data.len() < 64 {
                self.data.push(0);
            }
            self.transform();
            while self.data.len() < 56 {
                self.data.push(0);
            }
        }

        // Append to the padding the total message's length in bits and transform
        self.data.push((bitlen >> 56) as u8);
        self.data.push((bitlen >> 48) as u8);
        self.data.push((bitlen >> 40) as u8);
        self.data.push((bitlen >> 32) as u8);
        self.data.push((bitlen >> 24) as u8);
        self.data.push((bitlen >> 16) as u8);
        self.data.push((bitlen >>  8) as u8);
        self.data.push((bitlen >>  0) as u8);
        self.transform();

        // Since this implementation uses little endian byte ordering and SHA uses big endian,
        // reverse all the bytes when copying the final state to the output hash
        let mut hash: [u8; 32] = Default::default();
        for i in 0..4 {
            hash[i+ 0] = (self.state[0] >> 24-8*i as u32) as u8;
            hash[i+ 4] = (self.state[1] >> 24-8*i as u32) as u8;
            hash[i+ 8] = (self.state[2] >> 24-8*i as u32) as u8;
            hash[i+12] = (self.state[3] >> 24-8*i as u32) as u8;
            hash[i+16] = (self.state[4] >> 24-8*i as u32) as u8;
            hash[i+20] = (self.state[5] >> 24-8*i as u32) as u8;
            hash[i+24] = (self.state[6] >> 24-8*i as u32) as u8;
            hash[i+28] = (self.state[7] >> 24-8*i as u32) as u8;
        }
        hash
    }
}

fn sha256(message: &[u8]) -> [u8; 32] {
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
        state.update(&block[..diff].into_iter()
            .map(|b| *b)
            .collect::<Vec<_>>());
        if diff < 64 {
            break;
        }
    }

    let hash = state.finalize();

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
        .map(|b| *b)
        .collect::<Vec<_>>();

    let hash = sha256(&data);

    print!("hash: ");
    for h in hash.iter() {
        print!("{:02x}", h);
    }
    println!();
    assert_eq!(
        &hash,
        b"\x7f\x83\xb1\x65\x7f\xf1\xfc\x53\xb9\x2d\xc1\x81\x48\xa1\xd6\x5d\
          \xfc\x2d\x4b\x1f\xa3\xd6\x77\x28\x4a\xdd\xd2\x00\x12\x6d\x90\x69"
    );
}

