use crate::hash::{hash_group, hash_prime};
use crate::math::modpow_uint_int;
use blake2::{Blake2b, Digest};
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;

// Let G be a group of unknown order.
// Here both the prover and verifier are given (u, w, x) and
// the prover wants to convince the verifier that w = u^x holds in G.

pub type ExponentProof = BigUint;

pub type KnowledgeProof = (BigUint, BigUint, BigInt);

/// NI-PoE Prove
/// Assumes `u^x = w`
/// All operations are `mod n`.
pub fn ni_poe_prove(x: &BigUint, u: &BigUint, w: &BigUint, n: &BigUint) -> ExponentProof {
    debug_assert!(&u.modpow(x, n) == w, "invalid input");

    // l <- H_prime(x, u, w)
    let mut to_hash = x.to_bytes_be();
    to_hash.extend(&u.to_bytes_be());
    to_hash.extend(&w.to_bytes_be());

    let l = hash_prime::<_, Blake2b>(&to_hash);

    // q <- floor(x/l)
    let q = x.div_floor(&l);

    //Prover sends Q <- u^q ∈ G to the Verifier.
    u.modpow(&q, n)
}

/// NI-PoE Verify
/// Assumes `u^x = w`
/// All operations are `mod n`.
pub fn ni_poe_verify(
    x: &BigUint,
    u: &BigUint,
    w: &BigUint,
    q: &ExponentProof,
    n: &BigUint,
) -> bool {
    // l <- H_prime(x, u, w)
    let mut to_hash = x.to_bytes_be();
    to_hash.extend(&u.to_bytes_be());
    to_hash.extend(&w.to_bytes_be());

    let l = hash_prime::<_, Blake2b>(&to_hash);

    // r <- x mod l
    let r = x.mod_floor(&l);

    // Q^l u^r == w
    &((q.modpow(&l, &n) * &u.modpow(&r, &n)) % n) == w
}

//proof of knowledge of exponent, i.e. a proof that a computationally bounded prover knows the discrete logarithm between two elements in a group of unknown order. The proof is succinct in that the proof size and verification time is independent of the size of the discrete-log.

/// NI-PoKE2 Prove
/// assumes `u^x = w`
/// All operations are `mod n`.
pub fn ni_poke2_prove(
    x: impl Into<BigInt>,
    u: &BigUint,
    w: &BigUint,
    n: &BigUint,
) -> (BigUint, BigUint, BigInt) {
    let x: BigInt = x.into();

    debug_assert!(&modpow_uint_int(u, &x, n).unwrap() == w, "invalid input");

    // g <- H_G(u, w)
    let mut to_hash = u.to_bytes_be();
    to_hash.extend(&w.to_bytes_be());
    let g = hash_group::<_, Blake2b>(&to_hash, n);

    // z = g^x
    let z = modpow_uint_int(&g, &x, n).expect("invalid state");

    // l <- H_prime(u, w, z)
    to_hash.extend(&z.to_bytes_be());
    let l: BigInt = hash_prime::<_, Blake2b>(&to_hash).into();

    // alpha = H(u, w, z, l)
    to_hash.extend(&l.to_bytes_be().1);
    let alpha = BigUint::from_bytes_be(&Blake2b::digest(&to_hash)[..]);

    // q <- floor(x/l)
    // r <- x % l
    let (q, r) = x.div_rem(&l);

    // Q <- (ug^alpha)^q
    let q_big = modpow_uint_int(&(u * &g.modpow(&alpha, n)), &q, n).expect("invalid state");

    (z, q_big, r)
}

/// NI-PoKE2 Verify
/// assumes `u^x = w`
/// All operations are `mod n`
pub fn ni_poke2_verify(
    u: &BigUint,
    w: &BigUint,
    pi: &(BigUint, BigUint, BigInt),
    n: &BigUint,
) -> bool {
    // {z, Q, r} <- pi
    let (z, q_big, r) = pi;

    // g <- H_G(u, w)
    let mut to_hash = u.to_bytes_be();
    to_hash.extend(&w.to_bytes_be());
    let g = hash_group::<_, Blake2b>(&to_hash, n);

    // l <- H_prime(u, w, z)
    to_hash.extend(&z.to_bytes_be());
    let l = hash_prime::<_, Blake2b>(&to_hash);

    // alpha = H(u, w, z, l)
    to_hash.extend(&l.to_bytes_be());
    let alpha = BigUint::from_bytes_be(&Blake2b::digest(&to_hash)[..]);

    // Q^l(ug^alpha)^r
    let lhs: BigInt = ((q_big.modpow(&l, n)
        * modpow_uint_int(&(u * &g.modpow(&alpha, n)), &r, n).expect("invalid state"))
        % n)
        .into();

    // wz^alpha
    let z_alpha = z.modpow(&alpha, n);
    let rhs: BigInt = ((w * z_alpha) % n).into();

    lhs == rhs
}
pub type PoprodProof = (BigUint, BigUint, BigUint, BigUint);

/// NI-PoProd' Prove
pub fn ni_poprod_prove(
    g: &BigUint,
    h: &BigUint,
    y1: &BigUint,
    y2: &BigUint,
    x1: &BigUint,
    x2: &BigUint,
    z: &BigUint,
    n: &BigUint,
) -> PoprodProof {
    // l <- H_prime(g, h, y1, y2)
    let mut to_hash = g.to_bytes_be();
    to_hash.extend(&h.to_bytes_be());
    to_hash.extend(&y1.to_bytes_be());
    to_hash.extend(&y2.to_bytes_be());
    let l: BigUint = hash_prime::<_, Blake2b>(&to_hash).into();

    // (q1, q2, q3) = (x1/l, x2/l, z/l)
    // (r1, r2) = (x1 mod l, x2 mod l)
    let (q1, r1) = x1.div_rem(&l);
    let (q2, r2) = x2.div_rem(&l);
    let (q3, _) = z.div_rem(&l);

    // (Q1, Q2, r1, r2, r3) = (h^q1, h^q2 * g^q3)
    let q_big1 = h.modpow(&q1, n);
    let q_big2 = h.modpow(&q2, n) * &g.modpow(&q3, n) % n;

    (q_big1, q_big2, r1, r2) as PoprodProof
}

/// NI-PoProd3 Verify
pub fn ni_poprod_verify(
    g: &BigUint,
    h: &BigUint,
    y1: &BigUint,
    y2: &BigUint,
    pi: &PoprodProof,
    n: &BigUint,
) -> bool {
    let (q_big1, q_big2, r1, r2) = pi;

    let mut to_hash = g.to_bytes_be();
    to_hash.extend(&h.to_bytes_be());
    to_hash.extend(&y1.to_bytes_be());
    to_hash.extend(&y2.to_bytes_be());
    let l: BigUint = hash_prime::<_, Blake2b>(&to_hash).into();

    // r1, r2 < l
    let range_check = r1 < &l && r2 < &l;

    // r3 = r1 * r2 mod l
    let r3 = (r1 * r2) % &l;

    // Q1^l h^r1 = y1
    let q1_check = {
        let lhs = (q_big1.modpow(&l, n) * h.modpow(&r1, n)) % n;
        lhs == *y1
    };

    // Q2^l * h^r2 * g^r3 = y2
    let q2_check = {
        let tmp = q_big2.modpow(&l, n) * h.modpow(&r2, n) % n;
        let lhs = tmp * g.modpow(&r3, n) % n;
        lhs == *y2
    };

    range_check && q1_check && q2_check
}

#[cfg(test)]
mod tests {
    use super::*;

    use num_bigint::{RandBigInt, RandPrime};
    use num_traits::One;
    use rand::thread_rng;

    #[test]
    fn test_ni_poe() {
        let mut rng = thread_rng();
        for _ in 1..4 {
            for j in 1..10 {
                for k in 1..4 {
                    let p = rng.gen_prime(128);
                    let q = rng.gen_prime(128);
                    let n = p * q;

                    let mut x = BigUint::one();
                    for _ in 0..j {
                        x *= rng.gen_prime(256);
                    }
                    let u = rng.gen_biguint(k * 64);
                    let w = u.modpow(&x, &n);

                    let q = ni_poe_prove(&x, &u, &w, &n);
                    assert!(ni_poe_verify(&x, &u, &w, &q, &n))
                }
            }
        }
    }

    #[test]
    fn test_ni_poke2() {
        let mut rng = thread_rng();

        for i in 1..4 {
            for j in 1..4 {
                for k in 1..4 {
                    let n = rng.gen_biguint(i * 64);

                    let x = rng.gen_prime(j * 128);
                    let u = rng.gen_prime(k * 64);
                    let w = u.modpow(&x, &n);

                    let pi = ni_poke2_prove(x.clone(), &u, &w, &n);
                    assert!(ni_poke2_verify(&u, &w, &pi, &n));

                    let x_fake = rng.gen_prime(j * 128);
                    let w_fake = u.modpow(&x_fake, &n);
                    let pi_fake = ni_poke2_prove(x_fake.clone(), &u, &w_fake, &n);
                    assert!(!ni_poke2_verify(&u, &w, &pi_fake, &n));
                }
            }
        }
    }

    #[test]
    fn test_ni_poprod() {
        let mut rng = thread_rng();

        for i in 1..10 {
            let n = rng.gen_biguint(1024);

            let g = rng.gen_biguint(1024) % &n;
            let h = rng.gen_biguint(1024) % &n;

            let x1 = rng.gen_biguint(128);
            let x2 = rng.gen_biguint(128);
            let z = &x1 * &x2;

            // h^x1
            let y1 = h.modpow(&x1, &n);
            // h^x2 * g^z
            let y2 = h.modpow(&x2, &n) * g.modpow(&z, &n) % &n;

            let pi = ni_poprod_prove(&g, &h, &y1, &y2, &x1, &x2, &z, &n);
            assert!(ni_poprod_verify(&g, &h, &y1, &y2, &pi, &n));

            let z_fake = rng.gen_biguint(128) * rng.gen_biguint(128);
            let pi_fake = ni_poprod_prove(&g, &h, &y1, &y2, &x1, &x2, &z_fake, &n);
            assert!(!ni_poprod_verify(&g, &h, &y1, &y2, &pi_fake, &n));
        }
    }

    #[test]
    fn test_ni_poprod_acc() {
        let mut rng = thread_rng();

        for i in 1..10 {
            let n = rng.gen_biguint(1024);

            let g = rng.gen_biguint(1024) % &n;
            let g_j = rng.gen_biguint(1024) % &n;
            let a_j = rng.gen_prime(128);
            let b_j = rng.gen_prime(128);
            let A_j = g_j.modpow(&a_j, &n);
            let B_j = g_j.modpow(&b_j, &n);
            let mut u = &a_j * &b_j;
            let mut U_n = g.modpow(&u, &n);

            let pi = ni_poprod_prove(&g, &g_j, &A_j, &((&B_j * &U_n) % &n), &a_j, &b_j, &u, &n);
            assert!(ni_poprod_verify(
                &g,
                &g_j,
                &A_j,
                &((&B_j * &U_n) % &n),
                &pi,
                &n
            ));

            let mut u = &a_j * &b_j * &rng.gen_prime(128);
            let mut U_n = g.modpow(&u, &n);
            assert!(!ni_poprod_verify(
                &g,
                &g_j,
                &A_j,
                &((&B_j * &U_n) % &n),
                &pi,
                &n
            ));
        }
    }
}
