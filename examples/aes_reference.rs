//! AES example
//!
//! Based on implementations from here:
//! https://github.com/B-Con/crypto-algorithms
//! https://github.com/kokke/tiny-AES-c

use std::convert::TryFrom;


// AES constants

// sbox constants
const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
];

// The round constant word array, Rcon[i], contains the values given by
// x to the power (i-1) being powers of x (x is denoted as {02}) in the field GF(2^8)
const RCON: [u8; 11] = [
    0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36
];


// AES context
struct Aes {
    words: usize,
    rounds: usize,

    round_key: Vec<u8>,
    iv: [u8; 16],

    // current streaming state
    state: [u8; 16],
    si: usize,
}

impl Aes {
    pub fn new(key: &[u8], iv: &[u8]) -> Self {
        assert!(key.len() == 16 || key.len() == 24 || key.len() == 32);
        assert!(iv.len() == 16);

        let words = key.len() / 4;
        let rounds = 6 + words;

        let mut self_ = Aes {
            words,
            rounds,

            // will be filled in by key_expansion
            round_key: vec![],
            iv: <_>::try_from(iv).unwrap(),

            state: [0; 16],
            si: 16,
        };

        self_.round_key = self_.key_expansion(key);
        self_
    }

    /// This function produces Nb(Nr+1) round keys. The round keys are used in
    /// each round to decrypt the states.
    fn key_expansion(&mut self, key: &[u8]) -> Vec<u8> {
        let mut temp = [0u8; 4];
        let mut round_key = Vec::new();

        // The first round key is the key itself.
        for i in 0..self.words {
            round_key.push(key[i*4+0]);
            round_key.push(key[i*4+1]);
            round_key.push(key[i*4+2]);
            round_key.push(key[i*4+3]);
        }

        // All other round keys are found from the previous round keys.
        for i in self.words .. 4*(self.rounds+1) {
            let k = (i-1)*4;
            temp[0] = round_key[k+0];
            temp[1] = round_key[k+1];
            temp[2] = round_key[k+2];
            temp[3] = round_key[k+3];

            if i % self.words == 0 {
                // This function shifts the 4 bytes in a word to the left once.
                // [a0,a1,a2,a3] becomes [a1,a2,a3,a0]

                // Function RotWord()
                let t = temp[0];
                temp[0] = temp[1];
                temp[1] = temp[2];
                temp[2] = temp[3];
                temp[3] = t;

                // SubWord() is a function that takes a four-byte input word and
                // applies the S-box to each of the four bytes to produce an output word.

                // Function Subword()
                temp[0] = SBOX[temp[0] as usize];
                temp[1] = SBOX[temp[1] as usize];
                temp[2] = SBOX[temp[2] as usize];
                temp[3] = SBOX[temp[3] as usize];

                temp[0] = temp[0] ^ RCON[i/self.words];
            }

            if key.len() == 32 && i % self.words == 4 {
                // Function Subword()
                temp[0] = SBOX[temp[0] as usize];
                temp[1] = SBOX[temp[1] as usize];
                temp[2] = SBOX[temp[2] as usize];
                temp[3] = SBOX[temp[3] as usize];
            }

            let k = (i-self.words)*4;
            round_key.push(round_key[k+0] ^ temp[0]);
            round_key.push(round_key[k+1] ^ temp[1]);
            round_key.push(round_key[k+2] ^ temp[2]);
            round_key.push(round_key[k+3] ^ temp[3]);
        }

        round_key
    }

    // This function adds the round key to state.
    // The round key is added to the state by an XOR function.
    fn add_round_key(&self, round: usize, state: &mut [u8; 16]) {
        for i in 0..4 {
            for j in 0..4 {
                state[i*4+j] ^= self.round_key[round*16 + i*4 + j];
            }
        }
    }

    // The SubBytes Function Substitutes the values in the
    // state matrix with values in an S-box.
    fn sub_bytes(&self, state: &mut [u8; 16]) {
        for i in 0..4 {
            for j in 0..4 {
                state[i*4+j] = SBOX[state[i*4+j] as usize];
            }
        }
    }

    // The ShiftRows() function shifts the rows in the state to the left.
    // Each row is shifted with different offset.
    // Offset = Row number. So the first row is not shifted.
    fn shift_rows(&self, state: &mut [u8; 16]) {
        let mut temp: u8;

        // Rotate first row 1 columns to left
        temp         = state[0*4+1];
        state[0*4+1] = state[1*4+1];
        state[1*4+1] = state[2*4+1];
        state[2*4+1] = state[3*4+1];
        state[3*4+1] = temp;

        // Rotate second row 2 columns to left
        temp         = state[0*4+2];
        state[0*4+2] = state[2*4+2];
        state[2*4+2] = temp;

        temp         = state[1*4+2];
        state[1*4+2] = state[3*4+2];
        state[3*4+2] = temp;

        // Rotate third row 3 columns to left
        temp         = state[0*4+3];
        state[0*4+3] = state[3*4+3];
        state[3*4+3] = state[2*4+3];
        state[2*4+3] = state[1*4+3];
        state[1*4+3] = temp;
    }

    // MixColumns function mixes the columns of the state matrix
    fn mix_columns(&self, state: &mut [u8; 16]) {
        fn xtime(x: u8) -> u8 {
            (x<<1) ^ (((x>>7) & 1) * 0x1b)
        }

        for i in 0..4 {
            let tmp;
            let mut tm;
            let t = state[i*4+0];
            tmp   = state[i*4+0] ^ state[i*4+1] ^ state[i*4+2] ^ state[i*4+3] ;
            tm    = state[i*4+0] ^ state[i*4+1]; tm = xtime(tm); state[i*4+0] ^= tm ^ tmp ;
            tm    = state[i*4+1] ^ state[i*4+2]; tm = xtime(tm); state[i*4+1] ^= tm ^ tmp ;
            tm    = state[i*4+2] ^ state[i*4+3]; tm = xtime(tm); state[i*4+2] ^= tm ^ tmp ;
            tm    = state[i*4+3] ^ t ;           tm = xtime(tm); state[i*4+3] ^= tm ^ tmp ;
        }
    }

    /// Cipher is the main function that encrypts the PlainText.
    fn cipher(&self, state: &mut [u8; 16]) {
        // Add the First round key to the state before starting the self.rounds.
        self.add_round_key(0, state);

        // There will be Nr rounds.
        // The first Nr-1 rounds are identical.
        // These Nr rounds are executed in the loop below.
        // Last one without MixColumns()
        for round in 1.. {
            self.sub_bytes(state);
            self.shift_rows(state);
            if round == self.rounds {
                break;
            }
            self.mix_columns(state);
            self.add_round_key(round, state);
        }

        // Add round key to last round
        self.add_round_key(self.rounds, state);
    }

    #[allow(unused)]
    pub fn encrypt(&mut self, data: &mut [u8]) {
        for i in 0..data.len() {
            if self.si == self.state.len() {
                self.si = 0;

                // encrypt ctr
                let mut state = self.iv;
                self.cipher(&mut state);
                self.state = state;

                // increment ctr
                for bi in (0..self.iv.len()).rev() {
                    let (n, overflow) = self.iv[bi].overflowing_add(1);
                    self.iv[bi] = n;
                    if !overflow {
                        // no overflow, done incrementing
                        break;
                    }
                }
            }

            // xor result
            data[i] ^= self.state[self.si];
            self.si += 1;
        }
    }

    #[allow(unused)]
    pub fn decrypt(&mut self, data: &mut [u8]) {
        self.encrypt(data)
    }
}

/// convenience function for encrypting
#[allow(unused)]
fn aes_encrypt(key: &[u8], iv: &[u8], data: &mut [u8]) {
    let mut state = Aes::new(key, iv);
    state.encrypt(data);
}

/// convenience function for decrypting
#[allow(unused)]
fn aes_decrypt(key: &[u8], iv: &[u8], data: &mut [u8]) {
    // symmetric
    aes_encrypt(key, iv, data);
}

fn bench(key: &str, iv: &str, in_path: &str, out_path: &str) -> ! {
    use std::io::Read;
    use std::io::Write;

    let key = std::fs::read(key).unwrap();
    let iv = std::fs::read(iv).unwrap();

    let mut in_file = std::fs::File::open(in_path).unwrap();
    let mut out_file = std::fs::File::create(out_path).unwrap();
    let mut state = Aes::new(&key, &iv);
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
    // - National Institute of Standards and Technology Special Publication 800-38A 2001 ED
    const AES128_KEY: [u8; 16] = [
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c
    ];
    const AES128_IN: [u8; 64] = [
        0x87, 0x4d, 0x61, 0x91, 0xb6, 0x20, 0xe3, 0x26, 0x1b, 0xef, 0x68, 0x64, 0x99, 0x0d, 0xb6, 0xce,
        0x98, 0x06, 0xf6, 0x6b, 0x79, 0x70, 0xfd, 0xff, 0x86, 0x17, 0x18, 0x7b, 0xb9, 0xff, 0xfd, 0xff,
        0x5a, 0xe4, 0xdf, 0x3e, 0xdb, 0xd5, 0xd3, 0x5e, 0x5b, 0x4f, 0x09, 0x02, 0x0d, 0xb0, 0x3e, 0xab,
        0x1e, 0x03, 0x1d, 0xda, 0x2f, 0xbe, 0x03, 0xd1, 0x79, 0x21, 0x70, 0xa0, 0xf3, 0x00, 0x9c, 0xee
    ];
    const AES192_KEY: [u8; 24] = [
        0x8e, 0x73, 0xb0, 0xf7, 0xda, 0x0e, 0x64, 0x52, 0xc8, 0x10, 0xf3, 0x2b, 0x80, 0x90, 0x79, 0xe5,
        0x62, 0xf8, 0xea, 0xd2, 0x52, 0x2c, 0x6b, 0x7b
    ];
    const AES192_IN: [u8; 64] = [
        0x1a, 0xbc, 0x93, 0x24, 0x17, 0x52, 0x1c, 0xa2, 0x4f, 0x2b, 0x04, 0x59, 0xfe, 0x7e, 0x6e, 0x0b, 
        0x09, 0x03, 0x39, 0xec, 0x0a, 0xa6, 0xfa, 0xef, 0xd5, 0xcc, 0xc2, 0xc6, 0xf4, 0xce, 0x8e, 0x94, 
        0x1e, 0x36, 0xb2, 0x6b, 0xd1, 0xeb, 0xc6, 0x70, 0xd1, 0xbd, 0x1d, 0x66, 0x56, 0x20, 0xab, 0xf7, 
        0x4f, 0x78, 0xa7, 0xf6, 0xd2, 0x98, 0x09, 0x58, 0x5a, 0x97, 0xda, 0xec, 0x58, 0xc6, 0xb0, 0x50
    ];
    const AES256_KEY: [u8; 32] = [
        0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
        0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4
    ];
    const AES256_IN: [u8; 64] = [
        0x60, 0x1e, 0xc3, 0x13, 0x77, 0x57, 0x89, 0xa5, 0xb7, 0xa7, 0xf5, 0x04, 0xbb, 0xf3, 0xd2, 0x28, 
        0xf4, 0x43, 0xe3, 0xca, 0x4d, 0x62, 0xb5, 0x9a, 0xca, 0x84, 0xe9, 0x90, 0xca, 0xca, 0xf5, 0xc5, 
        0x2b, 0x09, 0x30, 0xda, 0xa2, 0x3d, 0xe9, 0x4c, 0xe8, 0x70, 0x17, 0xba, 0x2d, 0x84, 0x98, 0x8d, 
        0xdf, 0xc9, 0xc5, 0x8d, 0xb6, 0x7a, 0xad, 0xa6, 0x13, 0xc2, 0xdd, 0x08, 0x45, 0x79, 0x41, 0xa6
    ];
    const IV: [u8; 16] = [
        0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff
    ];
    const OUT: [u8; 64] = [
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
        0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
        0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
        0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10
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

    // test aes128
    let mut buf = Vec::from(&AES128_IN[..]);
    aes_encrypt(&AES128_KEY, &IV, &mut buf[..]);

    println!("aes128 encrypted:");
    print_buf(&buf);
    println!("expected:");
    print_buf(&OUT);
    assert_eq!(buf, OUT);

    // test aes192
    let mut buf = Vec::from(&AES192_IN[..]);
    aes_encrypt(&AES192_KEY, &IV, &mut buf[..]);

    println!("aes192 encrypted:");
    print_buf(&buf);
    println!("expected:");
    print_buf(&OUT);
    assert_eq!(buf, OUT);

    // test aes256
    let mut buf = Vec::from(&AES256_IN[..]);
    aes_encrypt(&AES256_KEY, &IV, &mut buf[..]);

    println!("aes256 encrypted:");
    print_buf(&buf);
    println!("expected:");
    print_buf(&OUT);
    assert_eq!(buf, OUT);
}
