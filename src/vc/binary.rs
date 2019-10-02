use crate::hash::hash_prime;
use crate::traits::*;
use blake2::Blake2b;
use byteorder::{BigEndian, ByteOrder};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use rand::CryptoRng;
use rand::Rng;
use std::marker::PhantomData;
use std::rc::Rc;
use crate::accumulator::PrimeHash;


#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
pub struct BinaryVectorCommitment<'a, A: 'a + UniversalAccumulator + BatchedAccumulator> {
    lambda: usize,
    n: usize,
    acc: A,
    pos: usize,
    _a: PhantomData<&'a A>,
    hash: Rc<PrimeHash>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Proof {
    Mem(BigUint),
    NonMem((BigUint, BigInt)),
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchProof(
    // membership proof
    (BigUint, BigUint),
    // non membership proof
    (BigUint, BigUint, (BigUint, BigUint, BigInt), BigUint),
);

#[derive(Clone, Debug)]
pub struct Config {
    pub lambda: usize,
    pub n: usize,
    pub ph: Rc<PrimeHash>,
}

impl<'a, A: 'a + UniversalAccumulator + BatchedAccumulator>
    BinaryVectorCommitment<'a, A>
{

}

impl<'a, A: 'a + UniversalAccumulator + BatchedAccumulator> StaticVectorCommitment<'a>
    for BinaryVectorCommitment<'a, A>
{
    type Domain = bool;
    type Proof = Proof;
    type BatchProof = BatchProof;
    type Config = Config;
    type Commitment = BigUint;
    type State = &'a BigUint;

    fn setup<G, R>(rng: &mut R, config: &Self::Config) -> Self
    where
        G: PrimeGroup,
        R: CryptoRng + Rng,
    {
        BinaryVectorCommitment {
            lambda: config.lambda,
            n: config.n,
            acc: A::setup::<G, _>(rng, config.lambda),
            pos: 0,
            _a: PhantomData,
            hash: Rc::clone(&config.ph),
        }
    }

    fn commit(&mut self, m: &[Self::Domain]) -> Self::Commitment {
        self.pos = 0;
        //println!("Committing to vec of size {}", m.len() );
        //m.iter().enumerate().for_each(|(i,x)| {println!("({}, {})", i, x);} );
        let primes = m
            .iter()
            .enumerate()
            .filter(|(_, &m_i)| m_i)
            .map(|(i, _)| {let x = self.pos + i; /*println!("Getting pos #{}", x); */  self.hash.get(x) })
            .collect::<Vec<_>>();

        self.pos = m.len();
        self.acc = self.acc.cleared(); // XXX: Reset everything
        self.acc.batch_add(&primes);

        self.acc.state().clone()
    }

    fn open(&self, b: &Self::Domain, i: usize) -> Self::Proof {
        let p_i = self.hash.get(i);

        if *b {
            Proof::Mem(self.acc.mem_wit_create(&p_i))
        } else {
            let p = self.acc.non_mem_wit_create(&p_i);
            Proof::NonMem(p)
        }
    }

    fn verify(&self, b: &Self::Domain, i: usize, pi: &Self::Proof) -> bool {
        let p_i = self.hash.get(i);

        if *b {
            match pi {
                Proof::Mem(v) => self.acc.ver_mem(v, &p_i),
                Proof::NonMem(_) => false,
            }
        } else {
            match pi {
                Proof::Mem(_) => false,
                Proof::NonMem(v) => self.acc.ver_non_mem(&v, &p_i),
            }
        }
    }

    fn batch_open(&self, b: &[Self::Domain], i: &[usize]) -> Self::BatchProof {
        debug_assert!(b.len() == i.len());

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

        let mut p_ones = BigUint::one();
        for j in ones {
            p_ones *= self.hash.get(i[j]);
        }

        let pi_i = if p_ones.is_one() {
            (BigUint::zero(), BigUint::zero())
        } else {
            self.acc.mem_wit_create_star(&p_ones)
        };

        let mut p_zeros = BigUint::one();
        for j in zeros {
            p_zeros *= self.hash.get(i[j]);
        }

        let pi_e = if p_zeros.is_one() {
            (
                BigUint::zero(),
                BigUint::zero(),
                (BigUint::zero(), BigUint::zero(), BigInt::zero()),
                BigUint::zero(),
            )
        } else {
            self.acc.non_mem_wit_create_star(&p_zeros)
        };

        BatchProof(pi_i, pi_e)
    }

    fn batch_verify(&self, b: &[Self::Domain], i: &[usize], pi: &Self::BatchProof) -> bool {
        debug_assert!(b.len() == i.len());

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

        let zeros = b
            .iter()
            .enumerate()
            .filter(|(_, b_j)| !**b_j)
            .map(|(j, _)| j);

        let mut p_zeros = BigUint::one();
        for j in zeros {
            p_zeros *= self.hash.get(i[j]);
        }

        if !p_zeros.is_one() && !self.acc.ver_non_mem_star(&p_zeros, &pi.1) {
            return false;
        }

        true
    }

    fn state(&'a self) -> Self::State {
        self.acc.state()
    }
}

impl<'a, A: 'a + UniversalAccumulator + BatchedAccumulator> DynamicVectorCommitment<'a>
    for BinaryVectorCommitment<'a, A>
{
    fn update(&mut self, b: &Self::Domain, b_prime: &Self::Domain, i: usize) {
        if b == b_prime {
            // Nothing to do
        } else if *b {
            self.acc.add(&self.hash.get(i));
        } else {
            self.acc.del(&self.hash.get(i)).expect("not a member");
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::accumulator::Accumulator;
    use crate::group::RSAGroup;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    #[test]
    fn test_binary_vc_basics() {
        let lambda = 128;
        let n = 1024;
        let mut rng = ChaChaRng::from_seed([0u8; 32]);

        let ph = Rc::new(PrimeHash::init(64));

        let config = Config { lambda, n,  ph };
        let mut vc = BinaryVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config);

        let mut val: Vec<bool> = (0..64).map(|_| rng.gen()).collect();
        // set two bits manually, to make checks easier
        val[2] = true;
        val[3] = false;

        vc.commit(&val);

        // open a set bit
        let comm = vc.open(&true, 2);
        assert!(vc.verify(&true, 2, &comm), "invalid commitment (bit set)");

        // open a set bit
        let comm = vc.open(&false, 3);
        assert!(
            vc.verify(&false, 3, &comm),
            "invalid commitment (bit not set)"
        );
    }

    #[test]
    fn test_binary_vc_batch() {
        let lambda = 128;
        let n = 1024;
        let mut rng = ChaChaRng::from_seed([0u8; 32]);

        let ph = Rc::new(PrimeHash::init(64));
        let config = Config { lambda, n,  ph };

        let mut vc = BinaryVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config);

        let val: Vec<bool> = (0..64).map(|_| rng.gen()).collect();
        vc.commit(&val);

        let committed = vec![val[2].clone(), val[3].clone(), val[9].clone()];
        let comm = vc.batch_open(&committed, &[2, 3, 9]);
        assert!(
            vc.batch_verify(&committed, &[2, 3, 9], &comm),
            "invalid commitment (bit set)"
        );
    }

    #[test]
    fn test_binary_vc_update() {
        let lambda = 128;
        let n = 1024;
        let mut rng = ChaChaRng::from_seed([0u8; 32]);

        let ph = Rc::new(PrimeHash::init(64));
        let config = Config { lambda, n,  ph };
        let mut vc = BinaryVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config);

        let mut val: Vec<bool> = (0..64).map(|_| rng.gen()).collect();
        // set two bits manually, to make checks easier
        val[2] = true;
        val[3] = false;

        vc.commit(&val);

        let comm = vc.open(&true, 2);
        assert!(vc.verify(&true, 2, &comm), "invalid commitment (bit set)");

        vc.update(&false, &true, 2);

        // ensure old commitment fails now
        assert!(
            !vc.verify(&true, 2, &comm),
            "commitment should be invalid (bit set)"
        );

        let comm_new = vc.open(&false, 2);
        assert!(
            vc.verify(&false, 2, &comm_new),
            "invalid commitment (bit not set)"
        );
    }
}
