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

    const N:usize = 1048; // modulus size
    const L:usize = 128; // Not sure we are using it.
    const K:usize = 1;
    const CHUNK_SZ:usize = 16;
    const N_CHUNKS:usize = 32;
    const SZ:usize = CHUNK_SZ*N_CHUNKS;

    const N_ITERS:usize = 2; // Set appropriately

    const SEED:[u8;32] = [1u8;32];

    fn flatten_chunks(all_vals:&Vec<bool>, chunks_I:&Vec<usize>, chk_sz:usize) -> (Vec<bool>, Vec<usize>)
    {
        let mut rslt_vals:Vec<bool> = vec![];
        let mut rslt_I:Vec<usize> = vec![];

        for chk_i in chunks_I.iter() {
            let chk_rng = (chk_i*chk_sz..(chk_i+1)*chk_sz);
            for j in chk_rng {
                rslt_I.push(j);
                rslt_vals.push(all_vals[j].clone());
            }
        }
        (rslt_vals, rslt_I)
    }

    fn collect_chunks(all_vals:&Vec<bool>, chunks_I:&Vec<usize>, chk_sz:usize) -> Vec<Vec<bool>>
    {
        let mut rslt_vals:Vec<Vec<bool>> = vec![];

        for chk_i in chunks_I.iter() {
            let chk_rng = (chk_i*chk_sz..(chk_i+1)*chk_sz);
            let mut cur_chk = vec![];
            for j in chk_rng {
                cur_chk.push(all_vals[j].clone());
            }
            rslt_vals.push(cur_chk);
        }
        rslt_vals
    }


    fn make_vc<'a, A>() -> (binary::BinaryVectorCommitment<'a, A>, yinyan::YinYanVectorCommitment<'a, A>)
    where A: accumulators::BatchedAccumulator + accumulators::UniversalAccumulator + accumulators::FromParts {
        let mut rng = ChaChaRng::from_seed(SEED);


        let config_bbf = binary::Config { lambda: L, n: N };
        let mut vc_bbf = binary::BinaryVectorCommitment::<A>::setup::<RSAGroup, _>(&mut rng, &config_bbf);

        let config_yy = yinyan::Config { lambda: L, k: K, n: N, precomp_l: CHUNK_SZ, size: SZ };
        let mut vc_yy = yinyan::YinYanVectorCommitment::<A>::setup::<RSAGroup, _>(&mut rng, &config_yy);

        (vc_bbf, vc_yy)
    }

    fn bench_bbf_commit(c: &mut Criterion) {
        // m_opn: opening size
        //let m_opn = 10;
        let m_opn = 16;

        let mut rng = ChaChaRng::from_seed(SEED);

        let (mut vc_bbf, mut vc_yy) = make_vc::<'_, Accumulator>();

        const FIXED_IDX:usize = 3;
        const FIXED_V:bool = false;

        // setting up BBF
        let mut val_bbf: Vec<bool> = (0..SZ).map(|_| rng.gen()).collect();
        val_bbf[FIXED_IDX] = FIXED_V;

        // setting up YY (Same values as val_bbf but in different format)
        let val_yy : Vec<Vec<bool>> = val_bbf.iter().map(|v| vec![*v]).collect();

        // Run Commit benchmarks
        {
            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            let (val_bbf2, val_yy2) = (val_bbf.clone(), val_yy.clone());

            c
                .bench_function("bench_bbf_commit", move |b| b.iter(|| bbf.commit(&val_bbf2)))
                .bench_function("bench_yinyan_commit_with_precomputation", move |b| b.iter(|| yy.commit_and_precompute(&val_yy2)));
        }

        vc_bbf.commit(&val_bbf);
        vc_yy.commit_and_precompute(&val_yy);

        // Run Open benchmarks
        {
            let chks_I:Vec<usize> = (0..m_opn).collect();
            /* map(
                |_| { let tmp:usize = rng.gen(); tmp % N_CHUNKS }
            ).collect(); */
            let (bbf_opn_vals, bbf_opn_I) = flatten_chunks(&val_bbf, &chks_I, CHUNK_SZ);
            let yy_opn_vals = collect_chunks(&val_bbf, &chks_I, CHUNK_SZ);

            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function("bench_bbf_batch_open",
                    move |b| b.iter(|| bbf.batch_open(&bbf_opn_vals, &bbf_opn_I) ))
                .bench_function("bench_yinyan_open_precomp",
                    move |b| b.iter(|| yy.batch_open_from_precomp(&yy_opn_vals, &chks_I) ));
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
