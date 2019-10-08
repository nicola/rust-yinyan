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

use std::rc::Rc;

//These benches are taken from various places.

mod vc_benches {
    use super::*;
    use accumulators::PrimeHash;
    use accumulators::group::RSAGroup;
    use accumulators::traits::{BatchedAccumulator, StaticAccumulator, StaticVectorCommitment};
    use accumulators::Accumulator;
    use accumulators::vc::{binary, yinyan};
    use num_bigint::RandPrime;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    // syntax: chunk_size, n_chunks, opn_size (in chunks)
    static PRE_PARAMS: &'static [(usize,usize,usize)] = &[
        (16, 32, 4),
    ];

    // syntax: (vector_size (bits), opn_size)
    static NON_PRE_PARAMS: &'static [(usize,usize)] = &[
        (512, 64),
        (1024, 128),
        (2048, 256),
        (4096, 512),
        (8192, 1024),
        (16384, 2048),
        (32768, 4096),
        (65536, 8192),
    ];


    const N:usize = 2048; // modulus size
    const L:usize = 128; // Not sure we are using it.
    const K:usize = 1;
    //const CHUNK_SZ:usize = 16;
    //const N_CHUNKS:usize = 32;
    //const SZ:usize = CHUNK_SZ*N_CHUNKS;

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


    fn make_vc<'a, A>(chunk_sz: usize, sz: usize, ph: &Rc<PrimeHash>) -> (binary::BinaryVectorCommitment<'a, A>, yinyan::YinYanVectorCommitment<'a, A>)
    where A: accumulators::BatchedAccumulator + accumulators::UniversalAccumulator + accumulators::FromParts {
        let mut rng = ChaChaRng::from_seed(SEED);


        let config_bbf = binary::Config { lambda: L, n: N, ph: ph.clone() };
        let mut vc_bbf =
            binary::BinaryVectorCommitment::<A>::setup::<RSAGroup, _>(&mut rng, &config_bbf);

        let config_yy = yinyan::Config { lambda: L, k: K, n: N, precomp_l: chunk_sz, size: sz, ph: ph.clone() };
        let mut vc_yy =
            yinyan::YinYanVectorCommitment::<A>::setup::<RSAGroup, _>(&mut rng, &config_yy);

        (vc_bbf, vc_yy)
    }


    // XXX: I do not think we need both bbf and yy here. The latter alone should be fine.
    fn bench_commit_pre_impl(c: &mut Criterion, tag:usize, chunk_sz:usize, n_chunks:usize, opn_sz:usize)
    {
        let sz = n_chunks * chunk_sz;
        let mut rng = ChaChaRng::from_seed(SEED);

        let myfmt = |s| -> String {
            format!("PRE_{}_CHKSZ={}_N_CHKS={}_OPNSZ={}", s, chunk_sz, n_chunks, opn_sz)
        };

        let ph = Rc::new(PrimeHash::init(sz));


        let (mut vc_bbf, mut vc_yy) =
            make_vc::<'_, Accumulator>(chunk_sz, sz, &ph);

        // setting up BBF
        let mut val_bbf: Vec<bool> = (0..sz).map(|_| rng.gen()).collect();

        // setting up YY (Same values as val_bbf but in different format)
        let val_yy : Vec<Vec<bool>> = val_bbf.iter().map(|v| vec![*v]).collect();

        // Run Commit benchmarks
        {
            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            let (val_bbf2, val_yy2) = (val_bbf.clone(), val_yy.clone());
            println!("There are {} values!", val_bbf2.len());

            c
                .bench_function(&myfmt("bench_bbf_commit"),
                    move |b| b.iter(|| bbf.commit(&val_bbf2)))
                .bench_function(&myfmt("bench_yinyan_commit_with_precomputation"),
                    move |b| b.iter(|| yy.commit_and_precompute(&val_yy2)));
        }

        vc_bbf.commit(&val_bbf);
        vc_yy.commit_and_precompute(&val_yy);

        let chks_I:Vec<usize> = (0..opn_sz).collect();
        let (bbf_opn_vals, bbf_opn_I) = flatten_chunks(&val_bbf, &chks_I, chunk_sz);
        let yy_opn_vals = collect_chunks(&val_bbf, &chks_I, chunk_sz);

        // Run Open benchmarks
        {
            let bbf_opn_vals2 = bbf_opn_vals.clone();
            let bbf_opn_I2 = bbf_opn_I.clone();
            let yy_opn_vals2 = yy_opn_vals.clone();
            let chks_I2 = chks_I.clone();

            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function(&myfmt("bench_bbf_batch_open"),
                    move |b| b.iter(|| bbf.batch_open(&bbf_opn_vals2, &bbf_opn_I2) ))
                .bench_function(&myfmt("bench_yinyan_open_precomp"),
                    move |b| b.iter(|| yy.batch_open_from_precomp(&yy_opn_vals2, &chks_I2) ));
        }

        let pi_bbf = vc_bbf.batch_open(&bbf_opn_vals, &bbf_opn_I);
        let pi_yy = vc_yy.batch_open_from_precomp(&yy_opn_vals, &chks_I);

        /*
        // Verify
        {
            let (bbf, yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function(&myfmt("bench_bbf_verify"),
                    move |b| b.iter(|| bbf.verify(&FIXED_V, FIXED_IDX, &pi_bbf) ))
                .bench_function(&myfmt("bench_yy_verify"),
                    move |b| b.iter(|| yy.batch_verify_bits(0, &bbf_opn_vals, &bbf_opn_I, &pi_yy) ));
        }
        */

    }

    fn bench_commit_pre(c: &mut Criterion) {
        // m_opn: opening size
        //let m_opn = 10;
        //let m_opn = 16;
        //let params = vec! [ (16, 32, 4) ]; // (chunk_sz, n_chunks, opn_sz)
        for (i,param) in PRE_PARAMS.iter().enumerate() {
            bench_commit_pre_impl(c, i, param.0, param.1, param.2);
        }

    }

    fn bench_commit_non_pre_impl(c: &mut Criterion, tag:usize, sz:usize, opn_sz:usize)
    {
        //let sz = n_chunks * chunk_sz;
        let mut rng = ChaChaRng::from_seed(SEED);

        let chunk_sz = 1; // we do not use this anyway

        let myfmt = |s| -> String {
            format!("NON_PRE_{}_VECSZ={}_OPNSZ={}", s, sz, opn_sz)
        };

        let ph = Rc::new(PrimeHash::init(sz));


        let (mut vc_bbf, mut vc_yy) =
            make_vc::<'_, Accumulator>(chunk_sz, sz, &ph);

        // setting up BBF
        let mut val_bbf: Vec<bool> = (0..sz).map(|_| rng.gen()).collect();

        // setting up YY (Same values as val_bbf but in different format)
        let val_yy : Vec<Vec<bool>> = val_bbf.iter().map(|v| vec![*v]).collect();

        // Run Commit benchmarks
        {
            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            let (val_bbf2, val_yy2) = (val_bbf.clone(), val_yy.clone());
            //println!("There are {} values!", val_bbf2.len());

            c
                .bench_function(&myfmt("bench_bbf_commit"),
                    move |b| b.iter(|| bbf.commit(&val_bbf2)))
                .bench_function(&myfmt("bench_yinyan_commit"),
                    move |b| b.iter(|| yy.commit(&val_yy2)));
        }

        vc_bbf.commit(&val_bbf);
        vc_yy.commit(&val_yy);

        let I:Vec<usize> = (0..opn_sz).collect();
        let bbf_opn_vals:Vec<bool> = I.iter().map(|i| val_bbf[*i].clone()).collect();
        let yy_opn_vals:Vec<Vec<bool>> = I.iter().map(|i| val_yy[*i].clone()).collect();


        // Run Open benchmarks
        {
            let bbf_opn_vals2 = bbf_opn_vals.clone();
            let yy_opn_vals2 = yy_opn_vals.clone();
            let I2_bbf = I.clone();
            let I2_yy = I.clone();

            let (mut bbf, mut yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function(&myfmt("bench_bbf_batch_open"),
                    move |b| b.iter(|| bbf.batch_open(&bbf_opn_vals2, &I2_bbf) ))
                .bench_function(&myfmt("bench_yinyan_batch_open"),
                    move |b| b.iter(|| yy.batch_open(&yy_opn_vals2, &I2_yy.clone()) ));
        }

        let pi_bbf = vc_bbf.batch_open(&bbf_opn_vals, &I);
        let pi_yy = vc_yy.batch_open(&yy_opn_vals, &I);


        // Verify
        {
            let I2_bbf = I.clone();
            let I2_yy = I.clone();

            let (bbf, yy) = (vc_bbf.clone(), vc_yy.clone());
            c
                .bench_function(&myfmt("bench_bbf_verify"),
                    move |b| b.iter(|| bbf.batch_verify(&bbf_opn_vals, &I2_bbf, &pi_bbf) ))
                .bench_function(&myfmt("bench_yy_verify"),
                    move |b| b.iter(|| yy.batch_verify(&yy_opn_vals, &I2_yy, &pi_yy) ));
        }


    }

    fn bench_commit_non_pre(c: &mut Criterion) {
        // m_opn: opening size
        //let m_opn = 10;
        //let m_opn = 16;
        //let params = vec! [ (16, 32, 4) ]; // (chunk_sz, n_chunks, opn_sz)
        for (i,param) in NON_PRE_PARAMS.iter().enumerate() {
            bench_commit_non_pre_impl(c, i, param.0, param.1);
        }

    }

    criterion_group! {
        name = vc_benches;
        config = Criterion::default().sample_size(N_ITERS);
        targets =
            /* bench_commit_pre, */ bench_commit_non_pre
    }

}


criterion_main!(
    vc_benches::vc_benches,
);
