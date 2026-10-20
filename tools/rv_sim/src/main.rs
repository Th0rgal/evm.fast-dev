use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::Path;
use std::time::Instant;

const INITIAL_PC: u64 = 0x8000_0000;
const NATIVE_PC: u64 = 0x8000_1190;
const HALT_PC: u64 = NATIVE_PC - 16;   // 0x80001180
const CCACHE_PC: u64 = NATIVE_PC - 32; // 0x80001170

const INPUT_START: u64 = 0x4000_0000;
const INPUT_END: u64 = 0x4800_0000;
const OUTPUT_START: u64 = 0xa041_0000;
const OUTPUT_END: u64 = 0xa042_0000;

const FFI_NAMES: [&str; 20] = [
    "bls_g1_add",
    "bls_g1_dbl",
    "bls_fp2_mul",
    "bls_fp2_sub",
    "bls_fp2_add",
    "bls_arith384",
    "bn_g1_add",
    "bn_g1_dbl",
    "bn_fp2_mul",
    "bn_fp2_sub",
    "bn_fp2_add",
    "bn_arith256",
    "blake2bround",
    "secpadd",
    "secpdbl",
    "arith256mod",
    "keccakf",
    "sha256f",
    "trap",
    "halt",
];

#[derive(Clone, Copy, Debug)]
struct MmioRec {
    entry_pc: u64,
    nbytes: u8,
    addr_reg: usize,
    addr_off: u64,
    reg: usize,
    exit_pc: u64,
    is_read: bool,
}

const MMIO_RECS: [MmioRec; 13] = [
    MmioRec { entry_pc: 5216,   nbytes: 1, addr_reg: 10, addr_off: 0, reg: 11, exit_pc: 5220,   is_read: false },
    MmioRec { entry_pc: 5260,   nbytes: 0, addr_reg: 13, addr_off: 0, reg: 12, exit_pc: 5264,   is_read: false },
    MmioRec { entry_pc: 5292,   nbytes: 0, addr_reg: 12, addr_off: 0, reg: 10, exit_pc: 5296,   is_read: false },
    MmioRec { entry_pc: 9888,   nbytes: 0, addr_reg: 10, addr_off: 0, reg: 11, exit_pc: 9892,   is_read: true  },
    MmioRec { entry_pc: 10184,  nbytes: 0, addr_reg: 12, addr_off: 0, reg: 12, exit_pc: 10188,  is_read: true  },
    MmioRec { entry_pc: 10268,  nbytes: 1, addr_reg: 5,  addr_off: 0, reg: 13, exit_pc: 10272,  is_read: false },
    MmioRec { entry_pc: 902772, nbytes: 1, addr_reg: 10, addr_off: 0, reg: 1,  exit_pc: 902776, is_read: false },
    MmioRec { entry_pc: 902972, nbytes: 1, addr_reg: 10, addr_off: 0, reg: 1,  exit_pc: 902976, is_read: false },
    MmioRec { entry_pc: 903172, nbytes: 1, addr_reg: 10, addr_off: 0, reg: 1,  exit_pc: 903176, is_read: false },
    MmioRec { entry_pc: 903372, nbytes: 1, addr_reg: 10, addr_off: 0, reg: 1,  exit_pc: 903376, is_read: false },
    MmioRec { entry_pc: 903572, nbytes: 1, addr_reg: 10, addr_off: 0, reg: 1,  exit_pc: 903576, is_read: false },
    MmioRec { entry_pc: 903772, nbytes: 1, addr_reg: 10, addr_off: 0, reg: 1,  exit_pc: 903776, is_read: false },
    MmioRec { entry_pc: 903972, nbytes: 1, addr_reg: 10, addr_off: 0, reg: 1,  exit_pc: 903976, is_read: false },
];

fn parse_hex_bytes_from_file(path: &Path, out: &mut Vec<u8>) {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("failed to read {:?}: {}", path, e));
    let bytes = text.as_bytes();
    let mut i = 0;
    while i + 3 < bytes.len() {
        if bytes[i] == b'0' && bytes[i + 1] == b'x' {
            let h1 = bytes[i + 2];
            let h2 = bytes[i + 3];
            let buf = [h1, h2];
            let s = std::str::from_utf8(&buf).unwrap();
            if let Ok(v) = u8::from_str_radix(s, 16) {
                out.push(v);
            }
            i += 4;
        } else {
            i += 1;
        }
    }
}

fn load_candidate_code(cand_dir: &Path) -> Vec<u8> {
    let mut code = Vec::with_capacity(960_000);
    for i in 0..=1 {
        parse_hex_bytes_from_file(&cand_dir.join(format!("Prefix{:03}.lean", i)), &mut code);
    }
    for i in 0..=220 {
        parse_hex_bytes_from_file(&cand_dir.join(format!("Bytes{:03}.lean", i)), &mut code);
    }
    for i in 0..=10 {
        parse_hex_bytes_from_file(&cand_dir.join(format!("Suffix{:03}.lean", i)), &mut code);
    }
    code
}

// Keccak-f[1600]
const KECCAK_RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];
const KECCAK_ROT: [u32; 24] = [1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44];
const KECCAK_PI: [usize; 24] = [10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1];

fn keccakf(st: &mut [u64; 25]) {
    for round in 0..24 {
        let mut bc = [0u64; 5];
        for i in 0..5 {
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        }
        for i in 0..5 {
            let t = bc[(i + 4) % 5] ^ bc[(i + 1) % 5].rotate_left(1);
            for j in (0..25).step_by(5) {
                st[j + i] ^= t;
            }
        }
        let mut t = st[1];
        for i in 0..24 {
            let j = KECCAK_PI[i];
            let tmp = st[j];
            st[j] = t.rotate_left(KECCAK_ROT[i]);
            t = tmp;
        }
        for j in (0..25).step_by(5) {
            let b = [st[j], st[j + 1], st[j + 2], st[j + 3], st[j + 4]];
            for i in 0..5 {
                st[j + i] ^= (!b[(i + 1) % 5]) & b[(i + 2) % 5];
            }
        }
        st[0] ^= KECCAK_RC[round];
    }
}

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

fn sha256_compress(state: &mut [u32; 8], block: &[u8; 64]) {
    let mut w = [0u32; 64];
    for i in 0..16 {
        w[i] = u32::from_be_bytes(block[4 * i..4 * i + 4].try_into().unwrap());
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    for i in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ ((!e) & g);
        let temp1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(SHA256_K[i]).wrapping_add(w[i]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let temp2 = s0.wrapping_add(maj);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(temp1);
        d = c;
        c = b;
        b = a;
        a = temp1.wrapping_add(temp2);
    }
    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

// BigInt helper for arithModBytes (limbs = 4 or 6): d = (a * b + c) mod m
fn bigint_mul_add_mod(a: &[u64], b: &[u64], c: &[u64], m: &[u64]) -> Vec<u64> {
    let k = a.len();
    // Compute prod = a * b + c in 2*k + 1 limbs of u64
    let mut prod = vec![0u64; 2 * k + 1];
    for i in 0..k {
        let c_val = c[i];
        prod[i] = c_val;
    }
    for i in 0..k {
        let mut carry: u128 = 0;
        for j in 0..k {
            let cur = (prod[i + j] as u128) + (a[i] as u128) * (b[j] as u128) + carry;
            prod[i + j] = cur as u64;
            carry = cur >> 64;
        }
        let mut idx = i + k;
        while carry > 0 {
            let cur = (prod[idx] as u128) + carry;
            prod[idx] = cur as u64;
            carry = cur >> 64;
            idx += 1;
        }
    }
    // Bit-by-bit long division prod % m
    let mut rem = vec![0u64; k + 1];
    let total_bits = prod.len() * 64;
    for bit_idx in (0..total_bits).rev() {
        let bit = (prod[bit_idx / 64] >> (bit_idx % 64)) & 1;
        // Shift rem left by 1
        let mut carry = bit;
        for r in rem.iter_mut() {
            let next_carry = *r >> 63;
            *r = (*r << 1) | carry;
            carry = next_carry;
        }
        // Check if rem >= m
        let mut ge = rem[k] > 0;
        if !ge {
            for i in (0..k).rev() {
                if rem[i] != m[i] {
                    ge = rem[i] > m[i];
                    break;
                }
            }
            // if equal, ge should be true!
            if (0..k).all(|i| rem[i] == m[i]) {
                ge = true;
            }
        }
        if ge {
            let mut borrow: u128 = 0;
            for i in 0..k {
                let sub = (m[i] as u128) + borrow;
                if (rem[i] as u128) >= sub {
                    rem[i] -= sub as u64;
                    borrow = 0;
                } else {
                    rem[i] = ((1u128 << 64) + (rem[i] as u128) - sub) as u64;
                    borrow = 1;
                }
            }
            rem[k] = rem[k].wrapping_sub(borrow as u64);
        }
    }
    rem.truncate(k);
    rem
}

const SECP_P: [u64; 4] = [
    0xFFFFFFFEFFFFFC2F,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
];

const BN254_P: [u64; 4] = [
    0x3c208c16d87cfd47,
    0x97816a916871ca8d,
    0xb85045b68181585d,
    0x30644e72e131a029,
];

const BLS12_P: [u64; 6] = [
    0xb9feffffffffaaab,
    0x1eabfffeb153ffff,
    0x6730d2a0f6b0f624,
    0x64774b84f38512bf,
    0x4b1ba7b6434bacd7,
    0x1a0111ea397fe69a,
];

fn bigint_add_mod(a: &[u64], b: &[u64], m: &[u64]) -> Vec<u64> {
    let mut one = vec![0u64; a.len()];
    one[0] = 1;
    bigint_mul_add_mod(a, &one, b, m)
}

fn bigint_mul_mod(a: &[u64], b: &[u64], m: &[u64]) -> Vec<u64> {
    let zero = vec![0u64; a.len()];
    bigint_mul_add_mod(a, b, &zero, m)
}

fn bigint_sub_mod(a: &[u64], b: &[u64], m: &[u64]) -> Vec<u64> {
    let k = a.len();
    let mut b_red = bigint_add_mod(b, &vec![0u64; k], m);
    // m - b_red
    let mut diff = vec![0u64; k];
    let mut borrow: u128 = 0;
    for i in 0..k {
        let sub = (b_red[i] as u128) + borrow;
        if (m[i] as u128) >= sub {
            diff[i] = m[i] - sub as u64;
            borrow = 0;
        } else {
            diff[i] = ((1u128 << 64) + (m[i] as u128) - sub) as u64;
            borrow = 1;
        }
    }
    b_red.copy_from_slice(&diff);
    bigint_add_mod(a, &b_red, m)
}

fn bigint_inv_mod(x: &[u64], m: &[u64]) -> Vec<u64> {
    let k = x.len();
    // exp = m - 2
    let mut exp = m.to_vec();
    if exp[0] >= 2 {
        exp[0] -= 2;
    } else {
        let mut borrow: u128 = 2;
        for i in 0..k {
            if (exp[i] as u128) >= borrow {
                exp[i] -= borrow as u64;
                break;
            } else {
                exp[i] = ((1u128 << 64) + (exp[i] as u128) - borrow) as u64;
                borrow = 1;
            }
        }
    }
    let mut res = vec![0u64; k];
    res[0] = 1;
    let mut base = bigint_add_mod(x, &vec![0u64; k], m);
    for bit_idx in 0..(k * 64) {
        if ((exp[bit_idx / 64] >> (bit_idx % 64)) & 1) == 1 {
            res = bigint_mul_mod(&res, &base, m);
        }
        base = bigint_mul_mod(&base, &base, m);
    }
    res
}

fn curve_add_limbs(p: &[u64], pt1: &[u64], pt2: &[u64]) -> Vec<u64> {
    let nl = p.len();
    let x1 = &pt1[0..nl];
    let y1 = &pt1[nl..2 * nl];
    let x2 = &pt2[0..nl];
    let y2 = &pt2[nl..2 * nl];
    let dy = bigint_sub_mod(y2, y1, p);
    let dx = bigint_sub_mod(x2, x1, p);
    let inv_dx = bigint_inv_mod(&dx, p);
    let lam = bigint_mul_mod(&dy, &inv_dx, p);
    let lam2 = bigint_mul_mod(&lam, &lam, p);
    let x3_tmp = bigint_sub_mod(&lam2, x1, p);
    let x3 = bigint_sub_mod(&x3_tmp, x2, p);
    let x1_x3 = bigint_sub_mod(x1, &x3, p);
    let lam_dx = bigint_mul_mod(&lam, &x1_x3, p);
    let y3 = bigint_sub_mod(&lam_dx, y1, p);
    let mut out = x3;
    out.extend_from_slice(&y3);
    out
}

fn curve_dbl_limbs(p: &[u64], pt: &[u64]) -> Vec<u64> {
    let nl = p.len();
    let x1 = &pt[0..nl];
    let y1 = &pt[nl..2 * nl];
    let mut three = vec![0u64; nl];
    three[0] = 3;
    let mut two = vec![0u64; nl];
    two[0] = 2;
    let x1_sq = bigint_mul_mod(x1, x1, p);
    let num = bigint_mul_mod(&three, &x1_sq, p);
    let den = bigint_mul_mod(&two, y1, p);
    let inv_den = bigint_inv_mod(&den, p);
    let lam = bigint_mul_mod(&num, &inv_den, p);
    let lam2 = bigint_mul_mod(&lam, &lam, p);
    let x3_tmp = bigint_sub_mod(&lam2, x1, p);
    let x3 = bigint_sub_mod(&x3_tmp, x1, p);
    let x1_x3 = bigint_sub_mod(x1, &x3, p);
    let lam_dx = bigint_mul_mod(&lam, &x1_x3, p);
    let y3 = bigint_sub_mod(&lam_dx, y1, p);
    let mut out = x3;
    out.extend_from_slice(&y3);
    out
}

fn complex_add_limbs(p: &[u64], f1: &[u64], f2: &[u64]) -> Vec<u64> {
    let nl = p.len();
    let mut out = bigint_add_mod(&f1[0..nl], &f2[0..nl], p);
    let im = bigint_add_mod(&f1[nl..2 * nl], &f2[nl..2 * nl], p);
    out.extend_from_slice(&im);
    out
}

fn complex_sub_limbs(p: &[u64], f1: &[u64], f2: &[u64]) -> Vec<u64> {
    let nl = p.len();
    let mut out = bigint_sub_mod(&f1[0..nl], &f2[0..nl], p);
    let im = bigint_sub_mod(&f1[nl..2 * nl], &f2[nl..2 * nl], p);
    out.extend_from_slice(&im);
    out
}

fn complex_mul_limbs(p: &[u64], f1: &[u64], f2: &[u64]) -> Vec<u64> {
    let nl = p.len();
    let x0 = &f1[0..nl];
    let x1 = &f1[nl..2 * nl];
    let y0 = &f2[0..nl];
    let y1 = &f2[nl..2 * nl];
    let x0y0 = bigint_mul_mod(x0, y0, p);
    let x1y1 = bigint_mul_mod(x1, y1, p);
    let mut out = bigint_sub_mod(&x0y0, &x1y1, p);
    let x0y1 = bigint_mul_mod(x0, y1, p);
    let x1y0 = bigint_mul_mod(x1, y0, p);
    let im = bigint_add_mod(&x0y1, &x1y0, p);
    out.extend_from_slice(&im);
    out
}

const BLAKE2_SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

fn blake_g(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

fn blake2b_round(idx: usize, v: &mut [u64; 16], m: &[u64; 16]) {
    let s = &BLAKE2_SIGMA[idx % 10];
    blake_g(v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
    blake_g(v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
    blake_g(v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
    blake_g(v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
    blake_g(v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
    blake_g(v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
    blake_g(v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
    blake_g(v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
}

fn sign_extend(val: u64, bits: u32) -> i64 {
    let shift = 64 - bits;
    ((val << shift) as i64) >> shift
}

const PAGE_SHIFT: u64 = 16; // 64 KiB pages
const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
const PAGE_MASK: u64 = (PAGE_SIZE as u64) - 1;

struct SparseMem {
    pages: HashMap<u64, Box<[u8; PAGE_SIZE]>>,
}

impl SparseMem {
    fn new() -> Self {
        Self { pages: HashMap::new() }
    }

    #[inline(always)]
    fn read_u8(&self, addr: u64) -> u8 {
        let p = addr >> PAGE_SHIFT;
        let off = (addr & PAGE_MASK) as usize;
        self.pages.get(&p).map_or(0, |page| page[off])
    }

    #[inline(always)]
    fn write_u8(&mut self, addr: u64, val: u8) {
        let p = addr >> PAGE_SHIFT;
        let off = (addr & PAGE_MASK) as usize;
        let page = self.pages.entry(p).or_insert_with(|| Box::new([0u8; PAGE_SIZE]));
        page[off] = val;
    }

    fn write_slice(&mut self, base: u64, data: &[u8]) {
        for (i, &b) in data.iter().enumerate() {
            self.write_u8(base + i as u64, b);
        }
    }

    fn read_slice(&self, base: u64, len: usize) -> Vec<u8> {
        (0..len).map(|i| self.read_u8(base + i as u64)).collect()
    }

    #[inline(always)]
    fn read_u16(&self, addr: u64) -> u16 {
        let mut b = [0u8; 2];
        for i in 0..2 { b[i] = self.read_u8(addr + i as u64); }
        u16::from_le_bytes(b)
    }

    #[inline(always)]
    fn read_u32(&self, addr: u64) -> u32 {
        let p = addr >> PAGE_SHIFT;
        let off = (addr & PAGE_MASK) as usize;
        if off + 4 <= PAGE_SIZE {
            if let Some(page) = self.pages.get(&p) {
                return u32::from_le_bytes(page[off..off + 4].try_into().unwrap());
            } else {
                return 0;
            }
        }
        let mut b = [0u8; 4];
        for i in 0..4 { b[i] = self.read_u8(addr + i as u64); }
        u32::from_le_bytes(b)
    }

    #[inline(always)]
    fn read_u64(&self, addr: u64) -> u64 {
        let p = addr >> PAGE_SHIFT;
        let off = (addr & PAGE_MASK) as usize;
        if off + 8 <= PAGE_SIZE {
            if let Some(page) = self.pages.get(&p) {
                return u64::from_le_bytes(page[off..off + 8].try_into().unwrap());
            } else {
                return 0;
            }
        }
        let mut b = [0u8; 8];
        for i in 0..8 { b[i] = self.read_u8(addr + i as u64); }
        u64::from_le_bytes(b)
    }

    #[inline(always)]
    fn write_u16(&mut self, addr: u64, val: u16) {
        for (i, &b) in val.to_le_bytes().iter().enumerate() {
            self.write_u8(addr + i as u64, b);
        }
    }

    #[inline(always)]
    fn write_u32(&mut self, addr: u64, val: u32) {
        for (i, &b) in val.to_le_bytes().iter().enumerate() {
            self.write_u8(addr + i as u64, b);
        }
    }

    #[inline(always)]
    fn write_u64(&mut self, addr: u64, val: u64) {
        let p = addr >> PAGE_SHIFT;
        let off = (addr & PAGE_MASK) as usize;
        if off + 8 <= PAGE_SIZE {
            let page = self.pages.entry(p).or_insert_with(|| Box::new([0u8; PAGE_SIZE]));
            page[off..off + 8].copy_from_slice(&val.to_le_bytes());
            return;
        }
        for (i, &b) in val.to_le_bytes().iter().enumerate() {
            self.write_u8(addr + i as u64, b);
        }
    }
}

struct Sim {
    pc: u64,
    regs: [u64; 32],
    mem: SparseMem,
    host: SparseMem,
}

impl Sim {
    fn new(code: &[u8], packed_input: &[u8]) -> Self {
        let mut mem = SparseMem::new();
        mem.write_slice(INITIAL_PC, code);

        // Host memory: 8B zero meta at 0x40000000, followed by packed_input ([8B LE len][blob][pad]) at 0x40000008
        let mut host = SparseMem::new();
        host.write_slice(INPUT_START + 8, packed_input);

        Self {
            pc: INITIAL_PC,
            regs: [0u64; 32],
            mem,
            host,
        }
    }

    #[inline(always)]
    fn set_reg(&mut self, rd: usize, val: u64) {
        if rd != 0 {
            self.regs[rd] = val;
        }
    }

    #[inline(always)]
    fn step_inst(&mut self) -> Result<(), String> {
        let inst = self.mem.read_u32(self.pc);
        let opcode = inst & 0x7f;
        let rd = ((inst >> 7) & 0x1f) as usize;
        let funct3 = (inst >> 12) & 0x7;
        let rs1 = ((inst >> 15) & 0x1f) as usize;
        let rs2 = ((inst >> 20) & 0x1f) as usize;
        let funct7 = (inst >> 25) & 0x7f;

        let v1 = self.regs[rs1];
        let v2 = self.regs[rs2];

        match opcode {
            0x37 => {
                let imm = sign_extend((inst & 0xffff_f000) as u64, 32) as u64;
                self.set_reg(rd, imm);
                self.pc = self.pc.wrapping_add(4);
            }
            0x17 => {
                let imm = sign_extend((inst & 0xffff_f000) as u64, 32) as u64;
                self.set_reg(rd, self.pc.wrapping_add(imm));
                self.pc = self.pc.wrapping_add(4);
            }
            0x6f => {
                let imm20 = (inst >> 31) & 1;
                let imm10_1 = (inst >> 21) & 0x3ff;
                let imm11 = (inst >> 20) & 1;
                let imm19_12 = (inst >> 12) & 0xff;
                let raw = (imm20 << 20) | (imm19_12 << 12) | (imm11 << 11) | (imm10_1 << 1);
                let offset = sign_extend(raw as u64, 21) as u64;
                let target = self.pc.wrapping_add(offset);
                self.set_reg(rd, self.pc.wrapping_add(4));
                self.pc = target;
            }
            0x67 => {
                let imm = sign_extend((inst >> 20) as u64, 12) as u64;
                let target = v1.wrapping_add(imm) & !1u64;
                self.set_reg(rd, self.pc.wrapping_add(4));
                self.pc = target;
            }
            0x63 => {
                let imm12 = (inst >> 31) & 1;
                let imm10_5 = (inst >> 25) & 0x3f;
                let imm4_1 = (inst >> 8) & 0xf;
                let imm11 = (inst >> 7) & 1;
                let raw = (imm12 << 12) | (imm11 << 11) | (imm10_5 << 5) | (imm4_1 << 1);
                let offset = sign_extend(raw as u64, 13) as u64;
                let taken = match funct3 {
                    0 => v1 == v2,
                    1 => v1 != v2,
                    4 => (v1 as i64) < (v2 as i64),
                    5 => (v1 as i64) >= (v2 as i64),
                    6 => v1 < v2,
                    7 => v1 >= v2,
                    _ => return Err(format!("Invalid branch funct3 {} at 0x{:x}", funct3, self.pc)),
                };
                self.pc = if taken { self.pc.wrapping_add(offset) } else { self.pc.wrapping_add(4) };
            }
            0x03 => {
                let imm = sign_extend((inst >> 20) as u64, 12) as u64;
                let addr = v1.wrapping_add(imm);
                let val = match funct3 {
                    0 => sign_extend(self.mem.read_u8(addr) as u64, 8) as u64,
                    1 => sign_extend(self.mem.read_u16(addr) as u64, 16) as u64,
                    2 => sign_extend(self.mem.read_u32(addr) as u64, 32) as u64,
                    3 => self.mem.read_u64(addr),
                    4 => self.mem.read_u8(addr) as u64,
                    5 => self.mem.read_u16(addr) as u64,
                    6 => self.mem.read_u32(addr) as u64,
                    _ => return Err(format!("Invalid load funct3 {} at 0x{:x}", funct3, self.pc)),
                };
                self.set_reg(rd, val);
                self.pc = self.pc.wrapping_add(4);
            }
            0x23 => {
                let imm11_5 = (inst >> 25) & 0x7f;
                let imm4_0 = (inst >> 7) & 0x1f;
                let raw = (imm11_5 << 5) | imm4_0;
                let imm = sign_extend(raw as u64, 12) as u64;
                let addr = v1.wrapping_add(imm);
                match funct3 {
                    0 => self.mem.write_u8(addr, v2 as u8),
                    1 => self.mem.write_u16(addr, v2 as u16),
                    2 => self.mem.write_u32(addr, v2 as u32),
                    3 => self.mem.write_u64(addr, v2),
                    _ => return Err(format!("Invalid store funct3 {} at 0x{:x}", funct3, self.pc)),
                }
                self.pc = self.pc.wrapping_add(4);
            }
            0x13 => {
                let imm = sign_extend((inst >> 20) as u64, 12) as u64;
                let shamt = ((inst >> 20) & 0x3f) as u32;
                let top6 = (inst >> 26) & 0x3f;
                let val = match funct3 {
                    0 => v1.wrapping_add(imm),
                    2 => if (v1 as i64) < (imm as i64) { 1 } else { 0 },
                    3 => if v1 < imm { 1 } else { 0 },
                    4 => v1 ^ imm,
                    6 => v1 | imm,
                    7 => v1 & imm,
                    1 => v1 << shamt,
                    5 => match top6 {
                        0x00 => v1 >> shamt,
                        0x10 => ((v1 as i64) >> shamt) as u64,
                        _ => return Err(format!("Invalid SRLI/SRAI at 0x{:x}", self.pc)),
                    },
                    _ => unreachable!(),
                };
                self.set_reg(rd, val);
                self.pc = self.pc.wrapping_add(4);
            }
            0x1b => {
                let imm = sign_extend((inst >> 20) as u64, 12) as u64;
                let shamt = ((inst >> 20) & 0x1f) as u32;
                let val = match funct3 {
                    0 => sign_extend((v1 as u32).wrapping_add(imm as u32) as u64, 32) as u64,
                    1 => sign_extend(((v1 as u32) << shamt) as u64, 32) as u64,
                    5 => match funct7 {
                        0x00 => sign_extend(((v1 as u32) >> shamt) as u64, 32) as u64,
                        0x20 => (((v1 as i32) >> shamt) as i64) as u64,
                        _ => return Err(format!("Invalid SRLIW/SRAIW at 0x{:x}", self.pc)),
                    },
                    _ => return Err(format!("Invalid OP-IMM-32 funct3 {} at 0x{:x}", funct3, self.pc)),
                };
                self.set_reg(rd, val);
                self.pc = self.pc.wrapping_add(4);
            }
            0x33 => {
                let shamt = (v2 & 0x3f) as u32;
                let val = match (funct7, funct3) {
                    (0x00, 0) => v1.wrapping_add(v2),
                    (0x20, 0) => v1.wrapping_sub(v2),
                    (0x00, 1) => v1 << shamt,
                    (0x00, 2) => if (v1 as i64) < (v2 as i64) { 1 } else { 0 },
                    (0x00, 3) => if v1 < v2 { 1 } else { 0 },
                    (0x00, 4) => v1 ^ v2,
                    (0x00, 5) => v1 >> shamt,
                    (0x20, 5) => ((v1 as i64) >> shamt) as u64,
                    (0x00, 6) => v1 | v2,
                    (0x00, 7) => v1 & v2,
                    (0x01, 0) => v1.wrapping_mul(v2),
                    (0x01, 1) => (((v1 as i64 as i128) * (v2 as i64 as i128)) >> 64) as u64,
                    (0x01, 2) => (((v1 as i64 as i128) * (v2 as u128 as i128)) >> 64) as u64,
                    (0x01, 3) => (((v1 as u128) * (v2 as u128)) >> 64) as u64,
                    (0x01, 4) => if v2 == 0 { u64::MAX } else if (v1 as i64) == i64::MIN && (v2 as i64) == -1 { v1 } else { ((v1 as i64) / (v2 as i64)) as u64 },
                    (0x01, 5) => if v2 == 0 { u64::MAX } else { v1 / v2 },
                    (0x01, 6) => if v2 == 0 { v1 } else if (v1 as i64) == i64::MIN && (v2 as i64) == -1 { 0 } else { ((v1 as i64) % (v2 as i64)) as u64 },
                    (0x01, 7) => if v2 == 0 { v1 } else { v1 % v2 },
                    _ => return Err(format!("Invalid OP funct7=0x{:x} funct3={} at 0x{:x}", funct7, funct3, self.pc)),
                };
                self.set_reg(rd, val);
                self.pc = self.pc.wrapping_add(4);
            }
            0x3b => {
                let shamt = (v2 & 0x1f) as u32;
                let w1 = v1 as u32;
                let w2 = v2 as u32;
                let val = match (funct7, funct3) {
                    (0x00, 0) => sign_extend(w1.wrapping_add(w2) as u64, 32) as u64,
                    (0x20, 0) => sign_extend(w1.wrapping_sub(w2) as u64, 32) as u64,
                    (0x00, 1) => sign_extend((w1 << shamt) as u64, 32) as u64,
                    (0x00, 5) => sign_extend((w1 >> shamt) as u64, 32) as u64,
                    (0x20, 5) => (((w1 as i32) >> shamt) as i64) as u64,
                    (0x01, 0) => sign_extend(w1.wrapping_mul(w2) as u64, 32) as u64,
                    (0x01, 4) => if w2 == 0 { u64::MAX } else if (w1 as i32) == i32::MIN && (w2 as i32) == -1 { sign_extend(w1 as u64, 32) as u64 } else { (((w1 as i32) / (w2 as i32)) as i64) as u64 },
                    (0x01, 5) => if w2 == 0 { u64::MAX } else { sign_extend((w1 / w2) as u64, 32) as u64 },
                    (0x01, 6) => if w2 == 0 { sign_extend(w1 as u64, 32) as u64 } else if (w1 as i32) == i32::MIN && (w2 as i32) == -1 { 0 } else { (((w1 as i32) % (w2 as i32)) as i64) as u64 },
                    (0x01, 7) => if w2 == 0 { sign_extend(w1 as u64, 32) as u64 } else { sign_extend((w1 % w2) as u64, 32) as u64 },
                    _ => return Err(format!("Invalid OP-32 funct7=0x{:x} funct3={} at 0x{:x}", funct7, funct3, self.pc)),
                };
                self.set_reg(rd, val);
                self.pc = self.pc.wrapping_add(4);
            }
            _ => return Err(format!("Unknown opcode 0x{:x} (inst=0x{:08x}) at 0x{:x}", opcode, inst, self.pc)),
        }
        Ok(())
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let repo_dir = args.get(1).map(|s| s.as_str()).unwrap_or("/var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev");
    let input_path = args.get(2).map(|s| s.as_str()).unwrap_or("/tmp/ssz_cases/minimal.bin");

    let t0 = Instant::now();
    let cand_dir = Path::new(repo_dir).join("submission/InitECandidate");
    let code = load_candidate_code(&cand_dir);
    println!("Loaded InitECandidate.code: {} bytes in {:?}", code.len(), t0.elapsed());

    let packed_input = fs::read(input_path).expect("failed to read input_path");
    println!("Loaded {}: {} bytes", input_path, packed_input.len());

    let mut mmio_map: HashMap<u64, MmioRec> = HashMap::new();
    for rec in MMIO_RECS {
        mmio_map.insert(NATIVE_PC + rec.entry_pc, rec);
    }

    let mut ext_map: HashMap<u64, usize> = HashMap::new();
    for i in 0..20 {
        ext_map.insert(NATIVE_PC - 16 * (3 + i as u64), i);
    }

    let mut sim = Sim::new(&code, &packed_input);
    let mut k_steps: u64 = 0;
    let mut ffi_counts: BTreeMap<String, u64> = BTreeMap::new();
    let mut pc_buckets: BTreeMap<u64, u64> = BTreeMap::new();
    let mut reached_native = false;

    let run_start = Instant::now();
    loop {
        if !reached_native && sim.pc == NATIVE_PC {
            reached_native = true;
            println!(
                "Reached nativePc (0x{:x}) at k_steps = {} (x10=0x{:x}, x11=0x{:x}, x12=0x{:x}, x13=0x{:x})",
                sim.pc, k_steps, sim.regs[10], sim.regs[11], sim.regs[12], sim.regs[13]
            );
        }

        // Check evaluateTargetHOL dispatch order:
        if let Some(&mmio) = mmio_map.get(&sim.pc) {
            let addr = sim.regs[mmio.addr_reg].wrapping_add(mmio.addr_off);
            let width = if mmio.nbytes == 0 { 8 } else { mmio.nbytes as usize };
            if mmio.is_read {
                *ffi_counts.entry(format!("sharedMem.read(w={})", width)).or_insert(0) += 1;
                let mut val = 0u64;
                for i in 0..width {
                    val |= (sim.host.read_u8(addr + i as u64) as u64) << (8 * i);
                }
                sim.set_reg(mmio.reg, val);
            } else {
                *ffi_counts.entry(format!("sharedMem.write(w={},pc={})", width, mmio.entry_pc)).or_insert(0) += 1;
                let val = sim.regs[mmio.reg];
                for i in 0..width {
                    sim.host.write_u8(addr + i as u64, ((val >> (8 * i)) & 0xff) as u8);
                }
            }
            sim.pc = NATIVE_PC + mmio.exit_pc;
            k_steps += 1;
            continue;
        }

        if let Some(&ext_idx) = ext_map.get(&sim.pc) {
            let name = FFI_NAMES[ext_idx];
            *ffi_counts.entry(format!("extCall.{}", name)).or_insert(0) += 1;
            let c_ptr = sim.regs[10];
            let c_len = sim.regs[11] as usize;
            let a_ptr = sim.regs[12];
            let a_len = sim.regs[13] as usize;
            k_steps += 1;
            if name == "halt" || name == "trap" {
                println!(
                    "TERMINAL FFI @{} at k_steps = {} in {:?} (c_len={}, a_len={})",
                    name, k_steps, run_start.elapsed(), c_len, a_len
                );
                let out_bytes = sim.host.read_slice(OUTPUT_START, 72);
                println!("Output[0..36]: {:02x?}", &out_bytes[0..36]);
                println!("Output[32] (ok): {} | Output[70] (err): {}", out_bytes[32], out_bytes[70]);
                break;
            }
            match name {
                "keccakf" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 200);
                    let mut st = [0u64; 25];
                    for i in 0..25 {
                        st[i] = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                    }
                    keccakf(&mut st);
                    for i in 0..25 {
                        sim.mem.write_u64(a_ptr + (i * 8) as u64, st[i]);
                    }
                }
                "sha256f" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 96);
                    // 4 words state (packed u32s: low u32 is first, high u32 is second), 8 words block (each word's low u32 is first BE u32)
                    let mut st = [0u32; 8];
                    for i in 0..4 {
                        let w = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                        st[2 * i] = w as u32;
                        st[2 * i + 1] = (w >> 32) as u32;
                    }
                    let mut blk = [0u8; 64];
                    for i in 0..64 {
                        blk[i] = sim.mem.read_u8(a_ptr + 32 + i as u64);
                    }
                    sha256_compress(&mut st, &blk);
                    for i in 0..4 {
                        let w = (st[2 * i] as u64) | ((st[2 * i + 1] as u64) << 32);
                        sim.mem.write_u64(a_ptr + (i * 8) as u64, w);
                    }
                }
                "arith256mod" | "bn_arith256" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 160);
                    let mut words = [0u64; 20];
                    for i in 0..20 {
                        words[i] = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                    }
                    let d = bigint_mul_add_mod(&words[0..4], &words[4..8], &words[8..12], &words[12..16]);
                    for i in 0..4 {
                        sim.mem.write_u64(a_ptr + ((16 + i) * 8) as u64, d[i]);
                    }
                }
                "bls_arith384" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 240);
                    let mut words = [0u64; 30];
                    for i in 0..30 {
                        words[i] = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                    }
                    let d = bigint_mul_add_mod(&words[0..6], &words[6..12], &words[12..18], &words[18..24]);
                    for i in 0..6 {
                        sim.mem.write_u64(a_ptr + ((24 + i) * 8) as u64, d[i]);
                    }
                }
                "secpadd" | "bn_g1_add" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 128);
                    let mut words = [0u64; 16];
                    for i in 0..16 {
                        words[i] = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                    }
                    let p = if name == "secpadd" { &SECP_P[..] } else { &BN254_P[..] };
                    let out = curve_add_limbs(p, &words[0..8], &words[8..16]);
                    for i in 0..8 {
                        sim.mem.write_u64(a_ptr + (i * 8) as u64, out[i]);
                    }
                }
                "secpdbl" | "bn_g1_dbl" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 64);
                    let mut words = [0u64; 8];
                    for i in 0..8 {
                        words[i] = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                    }
                    let p = if name == "secpdbl" { &SECP_P[..] } else { &BN254_P[..] };
                    let out = curve_dbl_limbs(p, &words[0..8]);
                    for i in 0..8 {
                        sim.mem.write_u64(a_ptr + (i * 8) as u64, out[i]);
                    }
                }
                "bn_fp2_add" | "bn_fp2_sub" | "bn_fp2_mul" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 128);
                    let mut words = [0u64; 16];
                    for i in 0..16 {
                        words[i] = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                    }
                    let out = match name {
                        "bn_fp2_add" => complex_add_limbs(&BN254_P, &words[0..8], &words[8..16]),
                        "bn_fp2_sub" => complex_sub_limbs(&BN254_P, &words[0..8], &words[8..16]),
                        _ => complex_mul_limbs(&BN254_P, &words[0..8], &words[8..16]),
                    };
                    for i in 0..8 {
                        sim.mem.write_u64(a_ptr + (i * 8) as u64, out[i]);
                    }
                }
                "bls_g1_add" | "bls_fp2_add" | "bls_fp2_sub" | "bls_fp2_mul" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 192);
                    let mut words = [0u64; 24];
                    for i in 0..24 {
                        words[i] = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                    }
                    let out = match name {
                        "bls_g1_add" => curve_add_limbs(&BLS12_P, &words[0..12], &words[12..24]),
                        "bls_fp2_add" => complex_add_limbs(&BLS12_P, &words[0..12], &words[12..24]),
                        "bls_fp2_sub" => complex_sub_limbs(&BLS12_P, &words[0..12], &words[12..24]),
                        _ => complex_mul_limbs(&BLS12_P, &words[0..12], &words[12..24]),
                    };
                    for i in 0..12 {
                        sim.mem.write_u64(a_ptr + (i * 8) as u64, out[i]);
                    }
                }
                "bls_g1_dbl" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 96);
                    let mut words = [0u64; 12];
                    for i in 0..12 {
                        words[i] = sim.mem.read_u64(a_ptr + (i * 8) as u64);
                    }
                    let out = curve_dbl_limbs(&BLS12_P, &words[0..12]);
                    for i in 0..12 {
                        sim.mem.write_u64(a_ptr + (i * 8) as u64, out[i]);
                    }
                }
                "blake2bround" => {
                    assert_eq!(c_len, 0);
                    assert_eq!(a_len, 264);
                    let idx = sim.mem.read_u64(a_ptr) as usize;
                    let mut st = [0u64; 16];
                    let mut msg = [0u64; 16];
                    for i in 0..16 {
                        st[i] = sim.mem.read_u64(a_ptr + 8 + (i * 8) as u64);
                        msg[i] = sim.mem.read_u64(a_ptr + 136 + (i * 8) as u64);
                    }
                    blake2b_round(idx, &mut st, &msg);
                    for i in 0..16 {
                        sim.mem.write_u64(a_ptr + 8 + (i * 8) as u64, st[i]);
                    }
                }
                other => {
                    panic!("Unimplemented extCall @{} at k_steps={}", other, k_steps);
                }
            }
            sim.pc = sim.regs[1];
            continue;
        }

        if sim.pc == HALT_PC {
            println!("Reached HALT_PC at k_steps = {} (x10 = {})", k_steps + 1, sim.regs[10]);
            k_steps += 1;
            break;
        }
        if sim.pc == CCACHE_PC {
            sim.pc = sim.regs[1];
            k_steps += 1;
            continue;
        }

        *pc_buckets.entry(sim.pc & !0xfff).or_insert(0) += 1;
        if let Err(e) = sim.step_inst() {
            println!("ERROR at k_steps = {}: {}", k_steps + 1, e);
            break;
        }
        k_steps += 1;
    }

    println!("\nFFI Call Summary:");
    for (k, v) in &ffi_counts {
        println!("  {:30}: {}", k, v);
    }
    let mut top_buckets: Vec<(u64, u64)> = pc_buckets.into_iter().collect();
    top_buckets.sort_by(|a, b| b.1.cmp(&a.1));
    println!("\nTop 10 4KB PC pages by instruction count:");
    for (page, count) in top_buckets.iter().take(10) {
        let pct = (*count as f64) * 100.0 / (k_steps.max(1) as f64);
        println!("  0x{:08x}..0x{:08x}: {:>10} ({:>5.2}%)", page, page + 0x1000, count, pct);
    }
}
