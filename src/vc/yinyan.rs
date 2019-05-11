use blake2::Blake2b;
use byteorder::{BigEndian, ByteOrder};
use num_bigint::{BigInt, BigUint};
use rand::CryptoRng;
use rand::Rng;
use std::marker::PhantomData;

use crate::hash::hash_prime;
use crate::traits::*;

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
pub struct YinYanVectorCommitment<'a, A: 'a + UniversalAccumulator + BatchedAccumulator> {
    lambda: usize, // security param
    k: usize,      // word size
    n: usize,      // rsa modulus size
    size: usize,   // max words in the vector
    uacc: A,
    accs: Vec<(A, A)>, // lenght of accs must be k
    _a: PhantomData<&'a A>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Commitment {
    Mem(BigUint),
    NonMem(BigUint),
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchCommitment(
    // membership proof
    (BigUint, BigUint),
    // non membership proof
    (BigUint, BigUint, (BigUint, BigUint, BigInt), BigUint),
);

#[derive(Clone, Debug)]
pub struct Config {
    pub lambda: usize,
    pub k: usize,
    pub n: usize,
    pub size: usize,
}

impl<'a, A: 'a + UniversalAccumulator + BatchedAccumulator> StaticVectorCommitment
    for YinYanVectorCommitment<'a, A>
{
    type Domain = Vec<bool>; // make sure this is of size k
    type Commitment = Vec<Commitment>;
    type BatchCommitment = BatchCommitment;
    type Config = Config;
    type State = Vec<(&'a BigUint, &'a BigUint)>;

    fn setup<G, R>(rng: &mut R, config: &Self::Config) -> Self
    where
        G: PrimeGroup,
        R: CryptoRng + Rng,
    {
        let mut vc = YinYanVectorCommitment {
            lambda: config.lambda,
            k: config.k,
            n: config.n,
            size: config.size,
            uacc: A::setup::<G, _>(rng, config.n),
            accs: (0..config.k)
                .map(|_| {
                    (
                        A::setup::<G, _>(rng, config.n),
                        A::setup::<G, _>(rng, config.n),
                    )
                })
                .collect(),
            _a: PhantomData,
        };

        // Specialization
        for i in 0..config.size {
            // TODO eventually do batchadd (check how we do it in commit)
            vc.uacc.add(&map_i_to_p_i(i));
        }

        vc
    }

    fn commit(&mut self, m: &[Self::Domain]) {
        assert!(m.len() == self.n); // TODO: only in the fixed case

        for (i, v) in m.iter().enumerate() {
            assert!(v.len() == self.k);
            let prime = map_i_to_p_i(i);

            // TODO: can be done with batch add!
            for (bit, acc) in v.iter().zip(self.accs.iter_mut()) {
                if *bit {
                    acc.1.add(&prime);
                } else {
                    acc.0.add(&prime);
                }
            }
        }

        // let pi = m.iter().map(|| {
        //     // proofs::ni_poprod_prove(x1: &BigUint, x2: &BigUint, z: &BigUint, g: &BigUint, h: &BigUint, y1: &BigUint, y2: &BigUint, n: &BigUint)
        // }).collect()

        // TODO: generate pi_prod
    }

    fn open(&self, b: &Self::Domain, i: usize) -> Self::Commitment {
        let p_i = map_i_to_p_i(i);

        b.iter()
            .zip(self.accs.iter())
            .map(|(bit, acc)| {
                if *bit {
                    Commitment::Mem(acc.1.mem_wit_create(&p_i))
                } else {
                    Commitment::Mem(acc.0.mem_wit_create(&p_i))
                }
            })
            .collect()
    }

    fn verify(&self, b: &Self::Domain, i: usize, pi: &Self::Commitment) -> bool {
        let p_i = map_i_to_p_i(i);

        b.iter()
            .zip(self.accs.iter())
            .zip(pi.iter())
            .all(|((bit, acc), w)| {
                if let Commitment::Mem(v) = w {
                    if *bit {
                        acc.1.ver_mem(v, &p_i)
                    } else {
                        acc.0.ver_mem(v, &p_i)
                    }
                } else {
                    false
                }
            })
    }

    fn state(&self) -> Self::State {
        unimplemented!()
        // self.accs.iter().map(|acc|
        //     (
        //         acc.0.state(),
        //         acc.1.state(),
        //     )
        // ).collect::<Vec<_>>()
    }

    fn batch_open(&self, b: &[Self::Domain], i: &[usize]) -> Self::BatchCommitment {
        unimplemented!();
    }

    fn batch_verify(&self, b: &[Self::Domain], i: &[usize], pi: &Self::BatchCommitment) -> bool {
        unimplemented!();
    }
}

impl<'a, A: 'a + UniversalAccumulator + BatchedAccumulator> DynamicVectorCommitment
    for YinYanVectorCommitment<'a, A>
{
    fn update(&mut self, b: &Self::Domain, b_prime: &Self::Domain, i: usize) {
        unimplemented!();
        // if b == b_prime {
        //     // Nothing to do
        // } else if *b {
        //     self.acc.add(&map_i_to_p_i(i));
        // } else {
        //     self.acc.del(&map_i_to_p_i(i)).expect("not a member");
        // }
    }
}

fn map_i_to_p_i(i: usize) -> BigUint {
    let mut to_hash = [0u8; 8];
    BigEndian::write_u64(&mut to_hash, i as u64);
    hash_prime::<_, Blake2b>(&to_hash)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::accumulator::Accumulator;
    use crate::group::RSAGroup;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;


    #[test]
    fn test_yinyan_vc_basics() {
        let lambda = 128;
        let n = 1024;
        let k = 2;
        let size = 4;

        let mut rng = ChaChaRng::from_seed([0u8; 32]);

        let config = Config { lambda, k, n, size };
        let mut vc =
            YinYanVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config);

        let mut val: Vec<Vec<bool>> = (0..n).map(|_| {
            (0..k).map(|_| rng.gen()).collect()
        }).collect();
        // set two bits manually, to make checks easier
        val[2] = vec![true, true];
        val[3] = vec![false, false];

        vc.commit(&val);

        // open a set bit
        let comm = vc.open(&vec![true, true], 2);
        assert!(vc.verify(&vec![true, true], 2, &comm), "invalid commitment (bit set)");

        assert!(!vc.verify(&vec![false, true], 2, &comm), "verification should not pass (bit set)");

        // open a set bit
        let comm = vc.open(&vec![false, false], 3);
        assert!(
            vc.verify(&vec![false, false], 3, &comm),
            "invalid commitment (bit not set)"
        );
    }
}
