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

    const N: usize = 1048;
    const L: usize = 128;

    // fn make_vc<'a>() -> (binary::BinaryVectorCommitment<'a>, yinyan::YinYanVectorCommitment<'a>) {
    //     let m = 10;
    //     let mut rng = ChaChaRng::from_seed([0u8; 32]);

    //     let config_bbf = binary::Config { lambda: L, n: N };
    //     let mut vc_bbf = binary::BinaryVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config_bbf);

    //     let config_yy = yinyan::Config { lambda: L, k: 1, n: N, size: m };
    //     let mut vc_yy = yinyan::YinYanVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config_yy);

    //    vc_yy, vc_bbf
    // }

    fn bench_bbf_commit(c: &mut Criterion) {
        let m = 10;
        let mut rng = ChaChaRng::from_seed([0u8; 32]);

        // setting up BBF
        let config_bbf = binary::Config { lambda: L, n: N };
        let mut vc_bbf = binary::BinaryVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config_bbf);
        let mut val_bbf: Vec<bool> = (0..m).map(|_| rng.gen()).collect();
        val_bbf[3] = true;

        // setting up YY
        let config_yy = yinyan::Config { lambda: L, k: 1, n: N, size: m };
        let mut vc_yy = yinyan::YinYanVectorCommitment::<Accumulator>::setup::<RSAGroup, _>(&mut rng, &config_yy);
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
            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function("bench_bbf_open", move |b| b.iter(|| bbf.open(&true, 3) ))
                .bench_function("bench_yinyan_open", move |b| b.iter(|| yy.open(&vec![true], 3) ));
        }

        let pi_bbf = vc_bbf.open(&true, 3);
        let pi_yy = vc_yy.open(&vec![true], 3);

        // Verify
        {
            let (bbf, yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function("bench_bbf_verify", move |b| b.iter(|| bbf.verify(&true, 3, &pi_bbf) ))
                .bench_function("bench_bbf_verify", move |b| b.iter(|| yy.verify(&vec![true], 3, &pi_yy) ));
        }

    }

    criterion_group! {
        name = vc_benches;
        config = Criterion::default().sample_size(3);
        targets =
            bench_bbf_commit,
    }

}


criterion_main!(
    vc_benches::vc_benches,
);
