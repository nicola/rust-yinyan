extern crate accumulators;
#[cfg(feature = "classgroup")]
extern crate classgroup;
extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;
extern crate rand;
extern crate rand_chacha;
#[macro_use]
extern crate criterion;
extern crate blake2;

use criterion::Criterion;

//These benches are taken from various places.

mod vc_benches {
    use super::*;
    use accumulators::group::RSAGroup;
    use accumulators::traits::{BatchedAccumulator, StaticAccumulator, StaticVectorCommitment};
    use accumulators::Accumulator;
    use accumulators::vc::binary;
    use num_bigint::RandPrime;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    const N: usize = 2048;
    const L: usize = 256;

    fn bench_bbf(c: &mut Criterion) {
        let m = 64;
        let mut rng = ChaChaRng::from_seed([0u8; 32]);

        let config = binary::Config { lambda: L, n: N };
        let mut vc = binary::BinaryVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config);

        let val: Vec<bool> = (0..64).map(|_| rng.gen()).collect();
        c.bench_function("bench_bbf", move |b| b.iter(|| vc.commit(&val)));
    }

    criterion_group! {
        name = vc_benches;
        config = Criterion::default();
        targets =
            bench_bbf,
    }

}


criterion_main!(
    vc_benches::vc_benches,
);
