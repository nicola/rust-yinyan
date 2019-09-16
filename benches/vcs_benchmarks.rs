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

use criterion::{Criterion, Benchmark};

//These benches are taken from various places.

mod vc_benches {
    use super::*;
    use accumulators::group::RSAGroup;
    use accumulators::traits::{BatchedAccumulator, StaticAccumulator, StaticVectorCommitment};
    use accumulators::Accumulator;
    use accumulators::vc::{binary, yinyan};
    use num_bigint::RandPrime;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    const N:usize = 1048;
    const L:usize = 128; // Not sure we are using it.
    const K:usize = 1;

    const N_ITERS:usize = 10;

    const SEED:[u8;32] = [1u8;32];


    fn make_vc<'a, A>() -> (binary::BinaryVectorCommitment<'a, A>, yinyan::YinYanVectorCommitment<'a, A>)
    where A: accumulators::BatchedAccumulator + accumulators::UniversalAccumulator + accumulators::FromParts {
        let mut rng = ChaChaRng::from_seed(SEED);


        let config_bbf = binary::Config { lambda: L, n: N };
        let mut vc_bbf = binary::BinaryVectorCommitment::<A>::setup::<RSAGroup, _>(&mut rng, &config_bbf);

        let config_yy = yinyan::Config { lambda: L, k: K, n: N, precomp_l: 1 };
        let mut vc_yy = yinyan::YinYanVectorCommitment::<A>::setup::<RSAGroup, _>(&mut rng, &config_yy);

        (vc_bbf, vc_yy)
    }

    fn bench_bbf_commit(c: &mut Criterion) {
        // m_opn: opening size
        //let m_opn = 10;

        let mut rng = ChaChaRng::from_seed(SEED);

        let (mut vc_bbf, mut vc_yy) = make_vc::<'_, Accumulator>();

        const FIXED_IDX:usize = 3;
        const FIXED_V:bool = false;

        // setting up BBF
        let mut val_bbf: Vec<bool> = (0..N).map(|_| rng.gen()).collect();
        val_bbf[FIXED_IDX] = FIXED_V;

        // setting up YY (Same values as val_bbf but in different format)
        let val_yy : Vec<Vec<bool>> = val_bbf.iter().map(|v| vec![*v]).collect();

        // Run Commit benchmarks
        {
            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            let (val_bbf2, val_yy2) = (val_bbf.clone(), val_yy.clone());

            c
                .bench_function("bench_bbf_commit", move |b| b.iter(|| bbf.commit(&val_bbf2)))
                .bench_function("bench_yinyan_commit", move |b| b.iter(|| yy.commit(&val_yy2)));
        }

        vc_bbf.commit(&val_bbf);
        vc_yy.commit(&val_yy);

        // Run Open benchmarks
        {
            // XXX: Should be opening something random
            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function("bench_bbf_open", move |b| b.iter(|| bbf.open(&FIXED_V, FIXED_IDX) ))
                .bench_function("bench_yinyan_open", move |b| b.iter(|| yy.open(&vec![FIXED_V], FIXED_IDX) ));
        }

        let pi_bbf = vc_bbf.open(&FIXED_V, FIXED_IDX);
        let pi_yy = vc_yy.open(&vec![FIXED_V], FIXED_IDX);

        // Verify
        {
            let (bbf, yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function("bench_bbf_verify", move |b| b.iter(|| bbf.verify(&FIXED_V, FIXED_IDX, &pi_bbf) ))
                .bench_function("bench_yy_verify", move |b| b.iter(|| yy.verify(&vec![FIXED_V], FIXED_IDX, &pi_yy) ));
        }

    }

    criterion_group! {
        name = vc_benches;
        config = Criterion::default().sample_size(N_ITERS);
        targets =
            bench_bbf_commit,
    }

}


criterion_main!(
    vc_benches::vc_benches,
);
