//! RSA example
//!
//! Based on several educational sources:
//! https://en.wikipedia.org/wiki/Montgomery_modular_multiplication
//! https://cp-algorithms.com/algebra/montgomery_multiplication.html
//! http://koclab.cs.ucsb.edu/teaching/cs154/docx/Notes7-Montgomery.pdf

use secret_u::*;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering;
use std::iter;
use std::cmp::min;
use std::convert::TryFrom;


/// Publically known exponent
const E: u32 = 65537;

/// Quick deterministic pseudorandom number generator for testing,
/// not at all cryptographically random
fn rand32() -> u32 {
    // using xorshift32
    static XORSHIFT32_STATE: AtomicU32 = AtomicU32::new(42);
    let mut x = XORSHIFT32_STATE.load(Ordering::Relaxed);
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    XORSHIFT32_STATE.store(x, Ordering::Relaxed);
    x
}

/// Pad using PKCS
fn pkcs_pad<'a>(data: &'a [SecretU8], len: usize) -> impl Iterator<Item=SecretU8> + 'a {
    assert!(data.len() <= len-3-8);
    iter::once(SecretU8::zero())
        .chain(iter::once(SecretU8::const_(2)))
        .chain(iter::repeat_with(|| SecretU8::const_(rand32() as u8)).take(len-3-data.len()))
        .chain(iter::once(SecretU8::zero()))
        .chain(data.iter().cloned())
}

/// Unpad, panicking if PKCS is not found, note this does declassify
/// portions of the array, but only known padding values
fn pkcs_unpad<'a>(data: &'a [SecretU8]) -> impl Iterator<Item=SecretU8> + 'a {
    let mut iter = data.iter().cloned();
    assert!(iter.next().unwrap().declassify() == 0);
    assert!(iter.next().unwrap().declassify() == 2);
    while iter.next().unwrap().declassify() != 0 {
        // skip random padding
    }

    // rest is unpadded
    iter
}


/// Convert to Montgomery form
///
/// Assuming n is odd and x = x mod n
///
fn mont_from(x: SecretU4096, n: SecretU4096) -> SecretU4096 {
    let mut x = x;
    for _ in 0..4096 {
        x <<= SecretU4096::one();
        x = x.clone().ge(n.clone()).select(
            x.clone() - n.clone(),
            x
        );
    }
    x
}

/// Find n' where n' = n^-1 mod r
fn mont_inv(n: SecretU4096) -> SecretU4096 {
    let mut n_i = SecretU4096::one();
    // log2(4096) = 12 iterations
    for _ in 0..12 {
        n_i *= SecretU4096::from(SecretU32::const_(2)) - n.clone()*n_i.clone();
    }
    n_i
}

/// Multiply integers in Montgomery form
fn mont_mul(a: SecretU4096, b: SecretU4096, n: SecretU4096, n_i: SecretU4096) -> SecretU4096 {
    // multiply using 2x width
    let x = SecretU8192::from(a) * SecretU8192::from(b);
    let q = SecretU4096x2::from_cast(x.clone()).extract(0) * n_i;
    let q = SecretU8192::from(q) * SecretU8192::from(n.clone());
    let a = SecretU4096x2::from_cast(x.clone()).extract(1) - SecretU4096x2::from_cast(q).extract(1);
    SecretI4096::from_cast(a.clone()).lt(SecretI4096::zero()).select(
        a.clone() + n,
        a
    )
}

/// Exponentiate an integer in Montgomery form with an exponent in normal form
fn mont_pow(a: SecretU4096, e: SecretU4096, n: SecretU4096, n_i: SecretU4096) -> SecretU4096 {
    let mut x = mont_from(SecretU4096::one(), n.clone());
    for i in (0..4096).rev() {
        x = mont_mul(x.clone(), x, n.clone(), n_i.clone());
        x = ((e.clone() >> SecretU4096::from(SecretU32::const_(i))) & SecretU4096::one())
            .eq(SecretU4096::one())
            .select(
                mont_mul(x.clone(), a.clone(), n.clone(), n_i.clone()),
                x
            );
    }
    x
}

/// Modular multiplication, (a * b) mod n
fn modmul(a: SecretU2048, b: SecretU2048, n: SecretU2048) -> SecretU2048 {
    let a = SecretU4096::from(a);
    let b = SecretU4096::from(b);
    let n = SecretU4096::from(n);

    // find n' and convert to Montgomery form
    let n_i = mont_inv(n.clone());
    let a_m = mont_from(a, n.clone());
    let b_m = mont_from(b, n.clone());

    // multiply
    let x_m = mont_mul(a_m, b_m, n.clone(), n_i.clone());

    // convert out of Montgomery form
    SecretU2048::from_cast(mont_mul(x_m, SecretU4096::one(), n, n_i))
}

/// Modular exponentiation, (a ^ e) mod n
fn modpow(a: SecretU2048, e: SecretU2048, n: SecretU2048) -> SecretU2048 {
    let a = SecretU4096::from(a);
    let e = SecretU4096::from(e);
    let n = SecretU4096::from(n);

    // find n' and convert to Mongomery form
    let n_i = mont_inv(n.clone());
    let a_m = mont_from(a, n.clone());

    // exponentiate
    let x_m = mont_pow(a_m, e, n.clone(), n_i.clone());

    // convert out of Montgomery form
    SecretU2048::from_cast(mont_mul(x_m, SecretU4096::one(), n, n_i))
}


/// Simple 2048-bit RSA implementation
struct Rsa {
    compiled_encrypt: Box<dyn Fn(&SecretU2048) -> SecretU2048>,
    compiled_decrypt: Option<Box<dyn Fn(&SecretU2048) -> SecretU2048>>,
}

impl Rsa {
    pub fn new(
        public_key: SecretU2048,
        private_key: Option<SecretU2048>,
    ) -> Self {
        // the variables of RSA
        // note most of these are in big-endian, so we need to flip bytes

        // modulus = public key
        let n = SecretU4096::from(public_key).eval();
        // public exponent
        let e = SecretU4096::from(SecretU32::const_(E));
        // private exponent = private key
        let d = private_key.map(|d| SecretU4096::from(d).eval());

        // precompute n'
        let n_i = mont_inv(n.clone()).eval();

        let encrypt = Box::new(compile!(|m: SecretU2048| -> SecretU2048 {
            let m_m = mont_from(SecretU4096::from(m), n.clone());
            let c_m = mont_pow(m_m, e.clone(), n.clone(), n_i.clone());
            SecretU2048::from_cast(mont_mul(c_m, SecretU4096::one(), n.clone(), n_i.clone()))
        }));

        let decrypt = d.clone().map(|d| -> Box<dyn Fn(&SecretU2048) -> SecretU2048> {
            Box::new(compile!(|c: SecretU2048| -> SecretU2048 {
                let c_m = mont_from(SecretU4096::from(c), n.clone());
                let m_m = mont_pow(c_m, d.clone(), n.clone(), n_i.clone());
                SecretU2048::from_cast(mont_mul(m_m, SecretU4096::one(), n.clone(), n_i.clone()))
            }))
        });

        Self {
            compiled_encrypt: encrypt,
            compiled_decrypt: decrypt,
        }
    }

    pub fn encrypt(&mut self, message: &[SecretU8]) -> Vec<SecretU8> {
        let mut ciphertext = Vec::new();

        let chunk_len = 256-3-8;
        for i in (0..message.len()).step_by(chunk_len) {
            // pad using PKCS
            let padded = pkcs_pad(&message[i .. min(i+chunk_len, message.len())], 256);

            // encrypt
            let mut m = SecretU8x256::zero();
            for (j, p) in padded.enumerate() {
                // reverse endianess here
                m = m.replace(256-1-j, p);
            }
            let c = SecretU8x256::from_cast((self.compiled_encrypt)(&SecretU2048::from_cast(m)));
            for j in 0..256 {
                // reverse endianess here
                ciphertext.push(c.clone().extract(256-1-j));
            }
        }

        ciphertext
    }

    pub fn decrypt(&mut self, ciphertext: &[SecretU8]) -> Vec<SecretU8> {
        let decrypt = match &self.compiled_decrypt {
            Some(decrypt) => decrypt,
            None => panic!("cannot decrypt, private key not provided"),
        };

        let mut message = Vec::new();

        assert!(ciphertext.len() % 256 == 0);
        for i in (0..ciphertext.len()).step_by(256) {
            // decrypt
            let mut c = SecretU8x256::zero();
            for j in 0..256 {
                // reverse endianess here
                c = c.replace(j, ciphertext[i+256-1-j].clone());
            }
            let m = SecretU8x256::from_cast((decrypt)(&SecretU2048::from_cast(c)));
            let mut padded = Vec::new();
            for j in 0..256 {
                // reverse endianess here
                padded.push(m.clone().extract(256-1-j));
            }

            // omit padding
            message.extend(pkcs_unpad(&padded));
        }

        message
    } 
}


fn bench(mode: &str, public_key: &str, private_key: &str, in_path: &str, out_path: &str) -> ! {
    use std::io::Read;
    use std::io::Write;

    match mode {
        "encrypt" => {
            let public_key = std::fs::read(public_key).unwrap();
            let public_key = SecretU8x256::new_lanes(<_>::try_from(public_key).ok().unwrap());
            let public_key = SecretU2048::from_cast(public_key.reverse_lanes());

            let mut in_file = std::fs::File::open(in_path).unwrap();
            let mut out_file = std::fs::File::create(out_path).unwrap();
            let mut state = Rsa::new(public_key, None);
            loop {
                let mut block = [0; 256-3-8];
                let diff = in_file.read(&mut block).unwrap();
                let message = block[..diff].iter()
                    .map(|b| SecretU8::new(*b))
                    .collect::<Vec<_>>();
                let ciphertext = state.encrypt(&message);
                let ciphertext = ciphertext.into_iter()
                    .map(|b| b.declassify())
                    .collect::<Vec<_>>();
                out_file.write_all(&ciphertext).unwrap();

                if diff < 256-3-8 {
                    break;
                }
            }
        }
        "decrypt" => {
            let public_key = std::fs::read(public_key).unwrap();
            let public_key = SecretU8x256::new_lanes(<_>::try_from(public_key).ok().unwrap());
            let public_key = SecretU2048::from_cast(public_key.reverse_lanes());
            let private_key = std::fs::read(private_key).unwrap();
            let private_key = SecretU8x256::new_lanes(<_>::try_from(private_key).ok().unwrap());
            let private_key = SecretU2048::from_cast(private_key.reverse_lanes());

            let mut in_file = std::fs::File::open(in_path).unwrap();
            let mut out_file = std::fs::File::create(out_path).unwrap();
            let mut state = Rsa::new(public_key, Some(private_key));
            loop {
                let mut block = [0; 256];
                let diff = in_file.read(&mut block).unwrap();
                let ciphertext = block[..diff].iter()
                    .map(|b| SecretU8::new(*b))
                    .collect::<Vec<_>>();
                let message = state.decrypt(&ciphertext);
                let message = message.into_iter()
                    .map(|b| b.declassify())
                    .collect::<Vec<_>>();
                out_file.write_all(&message).unwrap();

                if diff < 256 {
                    break;
                }
            }
        }
        _ => panic!("unknown mode: {:?}", mode),
    }

    std::process::exit(0);
}


fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() > 1 {
        bench(&args[1], &args[2], &args[3], &args[4], &args[5]);
    }

    // test multiplication/exponention to make sure groundwork works
    let x = modmul(
        SecretU2048::from(SecretU32::const_(0)),
        SecretU2048::from(SecretU32::const_(2)),
        SecretU2048::from(SecretU32::const_(3))
    );
    let x = SecretU32::from_cast(x).declassify();
    println!("0*2 (mod 3) = {}", x);
    assert_eq!(x, 0);

    let x = modmul(
        SecretU2048::from(SecretU32::const_(1)),
        SecretU2048::from(SecretU32::const_(2)),
        SecretU2048::from(SecretU32::const_(3))
    );
    let x = SecretU32::from_cast(x).declassify();
    println!("1*2 (mod 3) = {}", x);
    assert_eq!(x, 2);

    let x = modmul(
        SecretU2048::from(SecretU32::const_(2)),
        SecretU2048::from(SecretU32::const_(2)),
        SecretU2048::from(SecretU32::const_(3))
    );
    let x = SecretU32::from_cast(x).declassify();
    println!("2*2 (mod 3) = {}", x);
    assert_eq!(x, 1);

    let x = modpow(
        SecretU2048::from(SecretU32::const_(2)),
        SecretU2048::from(SecretU32::const_(2)),
        SecretU2048::from(SecretU32::const_(3))
    );
    let x = SecretU32::from_cast(x).declassify();
    println!("2^2 (mod 3) = {}", x);
    assert_eq!(x, 1);


    // test RSA
    const RSA_PUBLIC_KEY: [u8; 256] = [
        0xb4, 0x18, 0x30, 0x3c, 0xcf, 0x29, 0xda, 0x5d, 0xc4, 0x3f, 0xc5, 0x37, 0xff, 0xd6, 0x0b, 0xe9,
        0x00, 0x8a, 0x8e, 0x5b, 0x66, 0x3d, 0xfc, 0x00, 0xa2, 0x44, 0xf1, 0xca, 0xcf, 0xf1, 0x3a, 0xec,
        0xc9, 0xa3, 0xc4, 0xbc, 0xb2, 0xe2, 0x47, 0xf5, 0x80, 0xf9, 0x82, 0x34, 0x37, 0x2c, 0x5f, 0x26,
        0x46, 0x6d, 0xeb, 0x70, 0x05, 0xe9, 0xfe, 0x15, 0xf7, 0x10, 0xad, 0x61, 0x09, 0xbb, 0xbc, 0xb5,
        0xc0, 0xd2, 0x8c, 0xb3, 0x4c, 0xf5, 0x94, 0x5b, 0x03, 0x27, 0x7e, 0x5b, 0x45, 0x98, 0x16, 0xd2,
        0x58, 0xb2, 0xaf, 0x28, 0xfa, 0xf3, 0x39, 0xe2, 0x87, 0xb0, 0xb4, 0x68, 0xf7, 0x5d, 0xf8, 0x09,
        0x43, 0x76, 0xf3, 0x8a, 0xbc, 0x8b, 0x30, 0xa6, 0x6a, 0x24, 0xb4, 0x16, 0x75, 0x46, 0xd8, 0x7a,
        0xb7, 0x24, 0xe4, 0x77, 0x2f, 0x81, 0xf8, 0x4b, 0xc2, 0xb6, 0xbd, 0x6f, 0x99, 0x28, 0xf9, 0x7c,
        0xb5, 0x31, 0xaa, 0xdf, 0x43, 0xe3, 0x7b, 0x6e, 0xbc, 0x4b, 0xfd, 0x7b, 0x61, 0x67, 0x11, 0xf0,
        0x6c, 0x83, 0xaa, 0x0f, 0xb0, 0x14, 0x4f, 0xae, 0x37, 0x9e, 0x23, 0x6d, 0xb2, 0x1b, 0x8f, 0x05,
        0x62, 0xf6, 0x0c, 0x65, 0xb9, 0x28, 0xfb, 0x3c, 0xa5, 0xf6, 0xfb, 0x72, 0x23, 0x94, 0xa4, 0xb2,
        0x29, 0xdb, 0x50, 0x76, 0x82, 0x9b, 0xd8, 0x6c, 0x6d, 0x22, 0xd0, 0x30, 0x40, 0xda, 0xdf, 0xda,
        0xd7, 0x2e, 0xdf, 0x75, 0x35, 0x82, 0xb8, 0xa4, 0x29, 0xc7, 0x46, 0x96, 0x6d, 0xd5, 0xcc, 0xb3,
        0x1a, 0x0a, 0x3c, 0x95, 0x1d, 0x2e, 0x31, 0x85, 0x85, 0xaf, 0xe6, 0xd5, 0x8d, 0xe1, 0x6d, 0xe1,
        0x07, 0x96, 0x06, 0xc4, 0xf9, 0xc3, 0x6e, 0x37, 0xf8, 0xf7, 0x4a, 0x0f, 0x1f, 0xe2, 0x8a, 0xa9,
        0x84, 0x73, 0xac, 0xd3, 0xb7, 0x79, 0xb1, 0x86, 0x0e, 0x41, 0x84, 0x9a, 0x3d, 0x4e, 0xef, 0x6d,
    ];

    const RSA_PRIVATE_KEY: [u8; 256] = [
        0x7f, 0x0e, 0xf5, 0xb1, 0x61, 0x43, 0x18, 0xf1, 0xc0, 0x8c, 0x71, 0x3a, 0xe1, 0xff, 0x84, 0xa5,
        0x9d, 0xa1, 0x23, 0x70, 0x6e, 0x80, 0xda, 0xb3, 0x23, 0xc8, 0xda, 0x82, 0x09, 0x15, 0x1b, 0x4a,
        0x85, 0xb4, 0x4a, 0x10, 0x0b, 0x70, 0xc3, 0xed, 0xfc, 0x51, 0x8c, 0x40, 0x04, 0x91, 0x04, 0x8c,
        0x3f, 0x72, 0x3b, 0x81, 0xec, 0x5a, 0x3a, 0xce, 0x0a, 0x62, 0x34, 0xc0, 0x5a, 0x9a, 0x9e, 0x37,
        0xe8, 0xd3, 0x63, 0x3a, 0xf8, 0xd7, 0xe6, 0x14, 0x13, 0xf4, 0xa0, 0x1c, 0x0a, 0xcc, 0x93, 0x85,
        0x51, 0xd8, 0xb6, 0xe5, 0x85, 0xaf, 0x66, 0x2e, 0x61, 0x27, 0x15, 0x11, 0x5d, 0x3c, 0x69, 0xcb,
        0x37, 0x52, 0xcb, 0xde, 0x1c, 0xc9, 0x62, 0xc8, 0x75, 0xe8, 0x71, 0x39, 0xcb, 0x01, 0xf1, 0xa7,
        0x1a, 0x61, 0x27, 0xe2, 0xc2, 0x9c, 0xc2, 0xad, 0xc8, 0xb1, 0x1e, 0x93, 0x86, 0x8e, 0x36, 0xfd,
        0x4a, 0x62, 0x5a, 0xed, 0x7a, 0xef, 0x23, 0x8c, 0xb8, 0x9f, 0xb4, 0x70, 0x13, 0xce, 0x9c, 0x96,
        0x07, 0x4e, 0x3f, 0xfe, 0x89, 0x0e, 0x56, 0x72, 0x17, 0xed, 0xdd, 0x27, 0x04, 0x5d, 0xca, 0xfd,
        0x1e, 0xc8, 0xa5, 0xc0, 0xc1, 0x27, 0xed, 0x8c, 0x13, 0x88, 0x9a, 0x07, 0x36, 0x83, 0x09, 0xbd,
        0x37, 0xd6, 0x80, 0xa6, 0x41, 0xe2, 0x67, 0xb7, 0xa7, 0xff, 0x8e, 0xa6, 0xd9, 0x5d, 0xb0, 0x8b,
        0xae, 0xc5, 0x2f, 0x59, 0xb8, 0x1f, 0x23, 0x0f, 0x5f, 0x79, 0x6a, 0x00, 0xd3, 0xf6, 0x17, 0x69,
        0x69, 0x19, 0x52, 0xd9, 0x59, 0xba, 0x8a, 0xa7, 0xcf, 0xda, 0x01, 0xae, 0x29, 0x85, 0xd9, 0x68,
        0xdf, 0x44, 0x4d, 0x22, 0x80, 0x79, 0xd0, 0xd7, 0xf1, 0xb9, 0x7b, 0x30, 0xe0, 0xa5, 0x92, 0xdc,
        0x94, 0x23, 0x3c, 0xec, 0x55, 0x3c, 0x68, 0xb3, 0x8c, 0x20, 0xa7, 0xcd, 0xf0, 0x49, 0xc5, 0x8d, 
    ];

    const RSA_MESSAGE: [u8; 128] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
        0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
        0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
        0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
        0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f,
        0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
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

    // note we need to convert from big-endian to little-endian here
    let public_key  = SecretU2048::from_cast(SecretU8x256::new_lanes(RSA_PUBLIC_KEY).reverse_lanes());
    let private_key = SecretU2048::from_cast(SecretU8x256::new_lanes(RSA_PRIVATE_KEY).reverse_lanes());
    let mut rsa = Rsa::new(public_key, Some(private_key));
    let message = RSA_MESSAGE.iter()
        .map(|b| SecretU8::new(*b))
        .collect::<Vec<_>>();
    let ciphertext = rsa.encrypt(&message);
    let message = rsa.decrypt(&ciphertext);
    let ciphertext = ciphertext.iter()
        .map(|b| b.declassify())
        .collect::<Vec<_>>();
    let message = message.iter()
        .map(|b| b.declassify())
        .collect::<Vec<_>>();

    println!("rsa encrypted:");
    print_buf(&ciphertext);
    println!("rsa decrypted:");
    print_buf(&message);
    assert_eq!(message, RSA_MESSAGE);
}
