use blake2::Blake2b;
use byteorder::{BigEndian, ByteOrder};
use num_bigint::{BigInt, BigUint, RandBigInt};
use num_traits::cast::FromPrimitive;
use num_traits::identities::One;
use num_integer::Integer;
use num_traits::{Signed, Zero};

use crate::hash::hash_prime;
use crate::proofs;
use crate::traits::*;
use crate::math::{shamir_trick, root_factor_general};
use rand::{CryptoRng, Rng};
use std::marker::PhantomData;
use std::rc::Rc;

use crate::accumulator::PrimeHash;

// pub struct CachedAcc {
//     int_size_bits: usize,
//     g: BigUint,
//     n: BigUint,
//     root: BigUint,
//     elements: Vec<BigUint>
// }

// impl FromParts for CachedAcc {
//     fn from_parts(n: BigUint, g: BigUint) -> Self {
//         CachedAcc {
//             int_size_bits: n.bits(),
//             root: g.clone(),
//             g,
//             n,
//         }
//     }
//     fn g(&self) -> &BigUint {
//         &self.g
//     }
//     fn set(&self) -> &BigUint {
//         &self.set
//     }
// }

// impl StaticAccumulator for CachedAcc {
//     #[inline]
//     fn setup<T, R>(rng: &mut R, int_size_bits: usize) -> Self
//     where
//         T: PrimeGroup,
//         R: CryptoRng + Rng,
//     {
//         unimplemented!()
//     }

//     #[inline]
//     fn mem_wit_create(&self, x: &BigUint) -> BigUint {
//         unimplemented!()
//     }

//     #[inline]
//     fn ver_mem(&self, w: &BigUint, x: &BigUint) -> bool {
//         w.modpow(x, &self.n) == self.root
//     }

//     #[inline]
//     fn state(&self) -> &BigUint {
//         &self.root
//     }
//     #[inline]
//     fn add(&mut self, x: &BigUint) {
//         // assumes x is already a prime
//         self.root = self.root.modpow(x, &self.n);
//     }
// }

// Witness + PoE
#[derive(Debug, Clone)]
pub struct WitPoE
{
    pub wit: BigUint,
    pub poe: BigUint,
}

impl WitPoE {
    pub fn from_pair(p:&(BigUint, BigUint)) -> WitPoE
    {
        WitPoE { wit: p.0.clone(), poe: p.1.clone() }
    }

    pub fn to_pair(&self) -> (BigUint, BigUint)
    {
        (self.wit.clone(), self.poe.clone())
    }
}

type ProofBit = (BigUint, BigUint);
type Proof = Vec<ProofBit>; // proof for word

type BatchProofBit = (WitPoE, WitPoE);
type BatchProof = Vec<BatchProofBit>;

type Domain = Vec<bool>;


pub struct Commitment {
    pub states: Vec<(BigUint, BigUint)>,
    pub prods: Vec<proofs::PoprodProof>,
}



// produces two accumulators---one for the 0-vals; the other for the one-vals
fn partitioned_prime_prod(ph: &PrimeHash, vs:&Vec<bool>, I:&[usize] ) -> (BigUint, BigUint) {
    let pI = to_primes(ph, &I.to_vec());
    partitioned_prime_prod_primes(vs, &pI)
}

// same as above but start with primes
fn partitioned_prime_prod_primes(vs:&Vec<bool>, pI:&[BigUint] ) -> (BigUint, BigUint) {
    assert_eq!(vs.len(), pI.len());
    let mut rslt:Vec<BigUint> = vec![BigUint::one(), BigUint::one()];

    for (b, p_i) in vs.iter().zip(pI) {
        let b_idx = if *b {1} else {0};
        rslt[b_idx] = rslt[b_idx].clone() * p_i; // XXX: i is not the right idx
    }

    (rslt[0].clone(), rslt[1].clone())
}

fn all_primes(ph:&PrimeHash, n:usize) -> Vec<BigUint> {
    (0..n).map( |i| ph.get(i) ).collect()
}



fn compute_prod_for_chunk(ph: &PrimeHash, vals:&Vec<bool>, idx:usize, l:usize) -> BigUint {
    let range = (idx*l..(idx+1)*l);
    let ps = to_primes(ph, &range.collect());

    let mut prd = BigUint::one();
    for p in ps {
        prd *= p;
    }
    prd
}


#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
pub struct YinYanVectorCommitment<'a, A: 'a + UniversalAccumulator + BatchedAccumulator + FromParts>
{
    lambda: usize, // security param
    k: usize,      // word size
    size: usize,   // max words in the vector
    uacc: A,
    accs: Vec<(A, A)>, // lenght of accs must be k
    _a: PhantomData<&'a A>,
    prod_proofs: Vec<proofs::PoprodProof>,
    modulus: BigUint,
    precomp_l: usize, // each precomputed proof refers to a chunk of size precomp_l
    precomp_N: usize, // There are precomp_N chunks (and precomputed proofs)
    pi_precomp: Vec<Proof>, // precomputed proofs
    hash: Rc<PrimeHash>
}

#[derive(Clone, Debug)]
pub struct Config {
    pub lambda: usize,
    pub k: usize,
    pub n: usize,
    pub size: usize,
    pub precomp_l: usize,
    pub ph: Rc<PrimeHash>
}

impl<'a, A: 'a + UniversalAccumulator + BatchedAccumulator + FromParts>
    YinYanVectorCommitment<'a, A>
{
    pub fn reset(&mut self) {
        self.accs = self
            .accs
            .iter()
            .map(|acc| {
                (
                    A::from_parts(self.modulus.clone(), acc.0.g().clone()),
                    A::from_parts(self.modulus.clone(), acc.1.g().clone()),
                )
            })
            .collect();
        self.uacc = A::from_parts(self.modulus.clone(), self.uacc.g().clone());
        self.prod_proofs = vec![];
    }
    pub fn re_specialize(&mut self, size: usize) -> &BigUint {
        self.uacc = A::from_parts(self.modulus.clone(), self.uacc.g().clone());
        self.specialize(size)
    }

    pub fn specialize(&mut self, size: usize) -> &BigUint {
        // TODO: if already specialized skip first part
        for i in 0..size {
            // TODO: eventually do batchadd (check how we do it in commit)
            self.uacc.add(&self.hash.get(i));
        }

        self.uacc.state()
    }

    fn get_acc_for(&self, b:bool, pos_in_word:usize) -> BigUint
    {
        if b {
            self.accs[pos_in_word].1.state().clone()
        } else {
            self.accs[pos_in_word].0.state().clone()
        }
    }

    // Makes a trivial proof for a bit b from an accumulators by
    //  simply wrapping it into a pair appropriately
    fn mk_triv_pf(&self, b:bool, pos_in_word:usize, pf_for_b: BigUint) -> ProofBit
    {
        // get current accumulator for not(b)
        let acc = self.get_acc_for(!b, pos_in_word);

        if b { // this is a proof for 1
            (acc, pf_for_b)
        } else {
            (pf_for_b, acc)
        }
    }

    // this is used for "trivial" proofs
    fn bit_verify(&self, acc:&(A, A), bit:&bool, pf: &ProofBit, expn:&BigUint) -> bool {
        let (pf0, pf1) = pf;
        if *bit {
            acc.1.ver_mem(pf1, expn)
        } else {
            acc.0.ver_mem(pf0, expn)
        }
    }

    fn precompute_helper(&self, b:bool, ps:&Vec<BigUint>, vals:&Vec<bool>) -> Vec<BigUint>
    {
        let g = self.uacc.g();
        let l = self.precomp_l;

        let f = |idx:usize| if vals[idx]==b {ps[idx].clone()} else {BigUint::one()};

        // ps_b is the same as ps but "neutralizes" positions w/ 1-b as value
        let ps_b:Vec<BigUint> = (0..ps.len()).map(f).collect();
        let pfs_b = root_factor_general(g, ps_b.as_slice(), l, &self.modulus );
        pfs_b
    }

    pub fn precompute(&mut self, vals_:&[Domain])
    {
        // for now we force this
        assert_eq!(vals_.len(), self.size);
        assert_eq!(self.k, 1); // Temporarily supporting only simple bit domains.

        // let's start from square zero
        self.pi_precomp.clear();

        let vals:Vec<bool> = vals_.iter().map(|v| v[0]).collect();

        let l:usize = self.precomp_l;
        let ps = all_primes(&self.hash, self.size); // all primes
        let g = self.uacc.g();

        let pfs0 = self.precompute_helper(false, &ps, &vals);
        let pfs1 = self.precompute_helper(true, &ps, &vals);


        assert_eq!(pfs1.len(), self.precomp_N);

        for i in 0..self.precomp_N {
            // we have a vector of one element here as current impl is for k=1 only
            let aProof = vec![(pfs0[i].clone(), pfs1[i].clone())];
            self.pi_precomp.push( aProof );
        }
    }

    pub fn commit_and_precompute(&mut self, vals:&[Domain]) -> Commitment {
        let c = self.commit(vals);
        self.precompute(vals);
        c
    }

    // NB: i is an index between 0 and precomp_N-1. It's the index of a chunk!
    pub fn open_from_precomp(&self, i:usize) -> Proof
    {

        assert!(i < self.precomp_N);
        assert_eq!(self.k, 1); // Temporarily supporting only simple bit domains.

        self.pi_precomp[i].clone()
    }

    // I contains chunk indices
    pub fn batch_open_from_precomp(&self, chunks:&Vec<Vec<bool>>, I:&[usize]) -> Vec<(BigUint, BigUint)>
    {
        // XXX: Supporting only k=1 for now
        assert_eq!(self.k, 1);

        // NB: we assume m is a power of 2
        let m:usize = I.len();

        // vector of all proofs
        let prfs:Vec<(BigUint, BigUint)> = I.iter().map(
            |i| self.open_from_precomp(*i)[0].clone()
        ).collect();
        //let prods = I.iter().map(|i| self.prd_precomp[*i]).collect();

        let rslt_for_bit = self.aggregate_many_proofs_bit(&prfs, chunks, I);

        // we package it
        vec![rslt_for_bit]
    }

    fn aggregate_many_proofs_bit_helper(&self, prfs:&Vec<(BigUint, BigUint)>, part_prods:&Vec<(BigUint, BigUint)>) -> (BigUint, BigUint)
    {
        let m:usize = prfs.len();

        if m == 1 {
            return prfs[0].clone();
        }
        // We require m to be even
        assert!(m % 2 == 0);

        let m_prime = m.div_floor(&2);

        let mut new_prfs:Vec<(BigUint, BigUint)> = Vec::with_capacity(m_prime);
        let mut new_part_prods:Vec<(BigUint, BigUint)> = Vec::with_capacity(m_prime);


        for i in 0..m_prime {
            let L = 2*i; // left idx
            let R = 2*i+1; // right idx

            //println!("Going for iteration i={} with m={}", i, m);

            let alpha = part_prods[L].0.clone()*part_prods[R].0.clone();
            let beta = part_prods[L].1.clone()*part_prods[R].1.clone();
            new_part_prods.push( (alpha, beta) );

            let pi = self.aggregate_proofs_bit_part_prod(
                &prfs[L], part_prods[L].clone(),
                &prfs[R], part_prods[R].clone());
            new_prfs.push(pi);

            //println!("After aggregation of prod");
        }
        self.aggregate_many_proofs_bit_helper(&new_prfs, &new_part_prods)
    }

    fn aggregate_many_proofs_bit(&self, prfs:&Vec<(BigUint, BigUint)>, chunks:&Vec<Vec<bool>>, I:&[usize]) -> (BigUint, BigUint)
    {
        // we aggregate by chunk here
        // I is the subset of chunks we are opening
        let part_prods:Vec<(BigUint, BigUint)> = I.iter().zip(chunks).map(
            |(i,c)| {
                let chunk_start = i*self.precomp_l;
                let chunk_end = (i+1)*self.precomp_l;
                let range:Vec<usize>  = (chunk_start..chunk_end).collect();
                partitioned_prime_prod(&self.hash, c, &range )
            }
        ).collect();

        let prf = self.aggregate_many_proofs_bit_helper(prfs, &part_prods);
        prf
    }

    // This version is not for generic words but only for case k = 1 for now
    fn aggregate_proofs_bit(
        &self,
        pf1:&(BigUint, BigUint), vals1:&Vec<bool>, I1:&[usize],
        pf2:&(BigUint, BigUint), vals2:&Vec<bool>, I2:&[usize]
    ) -> (BigUint, BigUint) {
            self.aggregate_proofs_bit_primes(
                pf1, vals1, &to_primes(&self.hash, &I1.to_vec()), pf2, vals2, &to_primes(&self.hash, &I2.to_vec()))
    }

    // This version is not for generic words but only for case k = 1 for now
    fn aggregate_proofs_bit_primes(
        &self,
        pf1:&(BigUint, BigUint), vals1:&Vec<bool>, pI1:&[BigUint],
        pf2:&(BigUint, BigUint), vals2:&Vec<bool>, pI2:&[BigUint]
    ) -> (BigUint, BigUint) {

        // NB: We assume pI1 and pI2 are disjoint
        let pp1 = partitioned_prime_prod_primes(vals1, pI1);
        let pp2 = partitioned_prime_prod_primes(vals2, pI2);

        self.aggregate_proofs_bit_part_prod(pf1, pp1, pf2, pp2)
    }

    // This version is not for generic words but only for case k = 1 for now
    fn aggregate_proofs_bit_part_prod(
        &self,
        pf1:&(BigUint, BigUint), part_prod1:(BigUint, BigUint),
        pf2:&(BigUint, BigUint), part_prod2:(BigUint, BigUint)
    ) -> (BigUint, BigUint) {
        // NB: We assume pI1 and pI2 are disjoint
        let (a1, b1) = part_prod1;
        let (a2, b2) = part_prod2;

        let pf_zero = shamir_trick(&pf1.0, &pf2.0, &a1, &a2, &self.modulus).unwrap();
        let pf_one = shamir_trick(&pf1.1, &pf2.1, &b1, &b2, &self.modulus).unwrap();

        (pf_zero.clone(), pf_one.clone())
    }

    fn aggregate_proofs(
        &self,
        pf1:&Vec<(BigUint, BigUint)>, vals1:&[Domain], I1:&[usize],
        pf2:&Vec<(BigUint, BigUint)>, vals2:&[Domain], I2:&[usize]
    ) -> Vec<(BigUint, BigUint)> {
            let mut pfs:Vec<(BigUint, BigUint)> = vec![];
            for i in 0..self.k {
                let vals1_i = vals1.iter().map(|v| v[i]).collect();
                let vals2_i = vals2.iter().map(|v| v[i]).collect();
                let pf_i = self.aggregate_proofs_bit(
                    &pf1[i], &vals1_i, I1, &pf2[i], &vals2_i, I2);

                pfs.push(pf_i);
            }
            pfs
    }



    fn batch_open_bits(&self, pos_in_word:usize, b: &Vec<bool>, I: &[usize]) -> BatchProofBit {
        debug_assert!(b.len() == I.len());
        //let prf_zero:ProofBit;
        //let prf_one:ProofBit;

        let acc = &self.accs[pos_in_word];
        let ones = b
            .iter()
            .enumerate()
            .filter(|(_, b_j)| **b_j)
            .map(|(j, _)| j);

        let zeros = b
            .iter()
            .enumerate()
            .filter(|(_, b_j)| !*b_j)
            .map(|(j, _)| j);

        // make product
        let mut prd1 = BigUint::one();
        for j in ones {
            prd1 *= self.hash.get(I[j]);
        }

        let mut prd0 = BigUint::one();
        for j in zeros {
            prd0 *= self.hash.get(I[j]);
        }


        let mk_prf_bit_fn = |prd:BigUint, a:&A| {
            let raw_prf_bit = if prd.is_one() {
                (BigUint::zero(), BigUint::zero())
            } else {
                a.mem_wit_create_star(&prd)
            };
            WitPoE::from_pair(&raw_prf_bit)
        };


        let prf_one = mk_prf_bit_fn(prd1, &acc.1);
        let prf_zero = mk_prf_bit_fn(prd0, &acc.0);

        (prf_zero, prf_one)
    }

    fn batch_verify_bits(&self,
        pos_in_word:usize, b: &Vec<bool>, I: &[usize],
        pi: &BatchProofBit) -> bool {

            let acc = &self.accs[pos_in_word];

            let ones = b
                .iter()
                .enumerate()
                .filter(|(_, b_j)| **b_j)
                .map(|(j, _)| j);

            let zeros = b
                .iter()
                .enumerate()
                .filter(|(_, b_j)| !*b_j)
                .map(|(j, _)| j);

            // make product
            let mut prd1 = BigUint::one();
            for j in ones {
                prd1 *= self.hash.get(I[j]);
            }

            let mut prd0 = BigUint::one();
            for j in zeros {
                prd0 *= self.hash.get(I[j]);
            }

            let check_prf_bit_fn = |prd:BigUint, a:&A, prf:&(BigUint, BigUint)| {
                !prd.is_one() && !a.ver_mem_star(&prd, prf)
            };

            let fail_one = check_prf_bit_fn(prd1, &acc.1, &pi.1.to_pair());
            let fail_zero = check_prf_bit_fn(prd0, &acc.0, &pi.0.to_pair());

            !fail_one && !fail_zero
/*
            let ones = b
                .iter()
                .enumerate()
                .filter(|(_, b_j)| **b_j)
                .map(|(j, _)| j);

            let mut p_ones = BigUint::one();
            for j in ones {
                p_ones *= self.hash.get(i[j]);
            }

            if !p_ones.is_one() && !self.acc.ver_mem_star(&p_ones, &pi.0) {
                return false;
            }
            */

        // Old implementation: Temporarily not to be thrown away
        /*
        let (p0, p1) = partitioned_prime_prod(&self.hash, bits, I);
        let (pf0, pf1) = pi;
        let acc = &self.accs[pos_in_word];
        let rslt = acc.1.ver_mem(pf1, &p1) && acc.0.ver_mem(pf0, &p0);
        rslt
        */
    }
}

impl<'a, A: 'a + UniversalAccumulator + BatchedAccumulator + FromParts> StaticVectorCommitment<'a>
    for YinYanVectorCommitment<'a, A>
{
    type Domain = Domain; // make sure this is of size k
    type Proof = Proof;
    type BatchProof = BatchProof;
    type Config = Config;
    type State = Vec<(&'a BigUint, &'a BigUint)>;
    type Commitment = Commitment;

    fn setup<G, R>(rng: &mut R, config: &Self::Config) -> Self
    where
        G: PrimeGroup,
        R: CryptoRng + Rng,
    {
        let (modulus, _) = G::generate_primes(rng, config.n).unwrap();

        let two = BigUint::from_u64(2 as u64).unwrap();

        YinYanVectorCommitment {
            lambda: config.lambda,
            k: config.k,
            size: config.size,
            modulus: modulus.clone(),
            prod_proofs: vec![],
            uacc: A::from_parts(modulus.clone(), rng.gen_biguint(config.n)),
            accs: (0..config.k)
                .map(|_| {
                    let tmp = rng.gen_biguint(config.n);
                    let g = tmp.modpow(&two, &modulus);
                    (
                        A::from_parts(modulus.clone(), g.clone()),
                        A::from_parts(modulus.clone(), g),
                    )
                })
                .collect(),
            _a: PhantomData,
            precomp_l: config.precomp_l,
            precomp_N: config.size/config.precomp_l,
            pi_precomp: Vec::with_capacity( config.size/config.precomp_l), // size is precomp_N
            hash: Rc::clone(&config.ph),
        }
    }

    fn commit(&mut self, words: &[Self::Domain]) -> Self::Commitment {
        // i = 0..m (m number of words)
        for (i, v) in words.iter().enumerate() {
            debug_assert!(v.len() == self.k);
            debug_assert!(i < self.hash.max_sz);


            // p_i
            let prime = self.hash.get(i);

            // j = 0..k (k number of bits in each word)
            // TODO: can be done with batch add!
            for (bit, acc) in v.iter().zip(self.accs.iter_mut()) {
                if *bit {
                    // B_j
                    acc.1.add(&prime);
                } else {
                    // A_j
                    acc.0.add(&prime);
                }
            }
        }

        let g = self.uacc.g();
        let (U_n, u) = (self.uacc.state(), self.uacc.set());


        self.prod_proofs = self
            .accs
            .iter()
            .map(|acc| {
                let g_j = acc.0.g();
                debug_assert!(g_j == acc.1.g());
                let (A_j, a_j) = (acc.0.state(), acc.0.set());
                let (B_j, b_j) = (acc.1.state(), acc.1.set());
                let pi =
                    proofs::ni_poprod_prove(
                    g,
                    g_j,
                    A_j,
                    &((B_j * U_n) % &self.modulus),
                    a_j,
                    b_j,
                    u,
                    &self.modulus,
                );
                pi
            })
            .collect();

        Self::Commitment {
            states: self
                .state()
                .iter()
                .map(|acc| (acc.0.clone(), acc.1.clone()))
                .collect(),
            prods: self.prod_proofs.clone(),
        }
    }

    fn open(&self, wd: &Self::Domain, i: usize) -> Self::Proof {
        let p_i = self.hash.get(i);

        let proof: Proof = wd
            .iter().enumerate()
            .zip(self.accs.iter())
            .map( |((idx, bit), acc)| {
                let pf_bit = if *bit {
                        acc.1.mem_wit_create(&p_i)
                    } else {
                        acc.0.mem_wit_create(&p_i)
                    };
                self.mk_triv_pf(*bit, idx, pf_bit)
            } )
            .collect();

        proof
    }

    fn verify(&self, wd: &Self::Domain, i: usize, pi: &Self::Proof) -> bool {
        let p_i = self.hash.get(i);

        // Make sure proof is of the right size
        if self.prod_proofs.len() != self.k || pi.len() != self.k {
            return false;
        }

        // Verify accumulator proof
        let accs_check = wd
            .iter()
            .zip(self.accs.iter())
            .zip(pi.iter())
            .all(|((bit, acc), w)| {
                self.bit_verify(acc, bit, w, &p_i)
            });

        // Verify product proof
        let uacc_check = {
            let g = self.uacc.g();
            let U_n = self.uacc.state();
            self.accs
                .iter()
                .zip(self.prod_proofs.iter())
                .all(|(acc, prod)| {
                    let g_j = acc.0.g();
                    let (A_j, B_j) = (acc.0.state(), acc.1.state());
                    proofs::ni_poprod_verify(
                        g,                              // g
                        g_j,                            // h
                        A_j,                            // y1
                        &((B_j * U_n) % &self.modulus), // y2
                        prod,                           // pi
                        &self.modulus,
                    )
                })
        };

        accs_check && uacc_check
    }

    fn state(&'a self) -> Self::State {
        self.accs
            .iter()
            .map(|acc| (acc.0.state(), acc.1.state()))
            .collect()
    }

    fn batch_open(&self, ws: &[Self::Domain], I: &[usize]) -> Self::BatchProof {
        let mut prfs:BatchProof = vec![];
        for i in 0..self.k {
            let bs_i = ws.iter().map(|v| v[i]).collect();
            let pi = self.batch_open_bits(i, &bs_i, I);
            prfs.push(pi.clone());
        }
        prfs
    }

    fn batch_verify(&self, ws: &[Self::Domain], I: &[usize], pi: &Self::BatchProof) -> bool {
        for i in 0..self.k {
            let bs_i = ws.iter().map(|v| v[i]).collect();
            if !self.batch_verify_bits(i, &bs_i, I, &pi[i]) { return false; }
        }
        true
    }


}

// helper function that goes from a normal vec to something with bits;
fn liftv(src:&Vec<bool>) -> Vec<Vec<bool>>
{
    let dst:Vec<Vec<bool>> =
        src.iter().map(|x| vec![*x] ).collect();
    dst.clone()
}

fn liftb(val:&bool) -> Vec<bool>
{
    vec![*val]
}

// impl<'a, A: 'a + UniversalAccumulator + BatchedAccumulator + FromParts> DynamicVectorCommitment<'a>
//     for YinYanVectorCommitment<'a, A>
// {
//     fn update(&mut self, b: &Self::Domain, b_prime: &Self::Domain, i: usize) {
//         unimplemented!();
//         // if b == b_prime {
//         //     // Nothing to do
//         // } else if *b {
//         //     self.acc.add(&map_i_to_p_i(i));
//         // } else {
//         //     self.acc.del(&map_i_to_p_i(i)).expect("not a member");
//         // }
//     }
// }


// generalization of map_i_to_p_i for vectors
fn to_primes(ph:&PrimeHash, I:&Vec<usize>) -> Vec<BigUint> {
    I.iter().map(|i| ph.get(*i)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::accumulator::Accumulator;
    use crate::group::RSAGroup;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn fake_vector(m: usize, k: usize) -> Vec<Vec<bool>> {
        let mut rng = ChaChaRng::from_seed([0u8; 32]);
        let mut val: Vec<Vec<bool>> = (0..m)
            .map(|_| (0..k).map(|_| rng.gen()).collect())
            .collect();
        // set two bits manually, to make checks easier
        val[2] = vec![true, true];
        val[3] = vec![false, false];

        val
    }

    #[test]
    fn test_yinyan_vc_basics() {

        // Set up vector commitment
        let mut rng = ChaChaRng::from_seed([0u8; 32]);

        let config = Config {
            lambda: 128,
            k: 2,
            n: 1024,
            precomp_l: 1,
            size: 4,
            ph: Rc::new(PrimeHash::init(4))
        };

        let ph:&PrimeHash = &config.ph;


        // accept if we can do prime partition correctly
        let avec:Vec<bool> = vec![true, true, false, false];
        let (a, b) = partitioned_prime_prod(&config.ph, &avec, &[0,1, 2, 3]);
        assert_eq!(a, ph.get(2)*ph.get(3));
        assert_eq!(b, ph.get(0)*ph.get(1));

        let mut vc =
            YinYanVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config);



        // Specialize & commit to a vector
        let val = fake_vector(config.size, config.k);
        vc.specialize(val.len());
        vc.commit(&val);


        // Testing whether the aggregation works
        // Get two proofs and just merge BatchedAccumulator
        let proof = vc.open(&vec![true, true], 2);



        // Open a particular index
        let proof = vc.open(&vec![true, true], 2);


        // Accept a correct opening
        assert!(
            vc.verify(&vec![true, true], 2, &proof),
            "invalid commitment (bit set)"
        );

        // Reject an incorrect witness
        assert!(
            !vc.verify(&vec![false, false], 2, &proof),
            "verification should not pass"
        );

        // Reject a correct witness with an incorrect proof
        assert!(
            !vc.verify(&vec![false, false], 3, &proof),
            "verification should not pass"
        );

        // Reject a proof if we have a different specialization
        let mut vc_fake = vc.clone();
        vc_fake.re_specialize(val.len() + 1);
        assert!(
            !vc_fake.verify(&vec![true, true], 2, &proof),
            "union proof should not verify"
        );

        // Accept is re-specialized correctly
        vc_fake.re_specialize(val.len());
        assert!(
            vc_fake.verify(&vec![true, true], 2, &proof),
            "union proof should not verify"
        );

    }

    #[test]
    fn test_yinyan_vc_bit() {

        // Set up vector commitment
        let mut rng = ChaChaRng::from_seed([0u8; 32]);
        let ph = Rc::new(PrimeHash::init(4));

        let config = Config {
            lambda: 128,
            k: 1,
            n: 1024,
            precomp_l: 1,
            size: 4,
            ph: ph
        };

        // accept if we can do prime partition correctly
        let avec:Vec<bool> = vec![true, true, false, false];

        let mut vc =
            YinYanVectorCommitment::<Accumulator>::
                setup::<RSAGroup, _>(&mut rng, &config);
        vc.commit(&liftv(&avec));

        let opn = |i| {let val:bool = avec[i]; vc.open(&liftb(&val), i)};
        // test aggregate
        let pf0 = opn(0);
        let pf1 = opn(1);

        // should accept partition
        let pf_agg =
            vc.aggregate_proofs(
                &pf0, &[vec![avec[0]]], &[0],
                &pf1, &[vec![avec[1]]], &[1] );
        let agg_vals = &[liftb(&avec[0]), liftb(&avec[1])];
        //assert!(vc.batch_verify(agg_vals, &[0,1], &pf_agg));

    }

}
