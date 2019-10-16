extern crate accumulators;
extern crate rand_chacha;

use num_bigint::{BigInt, BigUint, IntoBigUint};
use num_traits::{One, Zero};




#[cfg(feature = "classgroup")]
extern crate classgroup;

//use crate::proofs;

extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;
extern crate rand;
//extern crate rand_chacha;
#[macro_use]

extern crate blake2;


use std::rc::Rc;


//use super::*;
use accumulators::PrimeHash;
use accumulators::group::RSAGroup;
use accumulators::traits::{BatchedAccumulator, StaticAccumulator, StaticVectorCommitment};
use accumulators::Accumulator;
use accumulators::vc::{binary, yinyan};
use accumulators::proofs;
use num_bigint::RandPrime;
use rand::{Rng, SeedableRng};
use crate::rand_chacha::ChaChaRng;

use std::time::{Duration, Instant};

struct ATimer {
    time: Instant,
    curDelta: Duration,
    T: u32,
}

impl ATimer {
    fn init(T:u32) -> ATimer {
         ATimer {time: Instant::now(), curDelta: Duration::new(0,0), T: T } 
         }
    fn start(&mut self) { self.time = Instant::now(); }
    fn stop(&mut self) { self.curDelta = self.time.elapsed(); }
    fn print(&self, msg:String) { println!("[Timing] {}: {:?}", msg, self.curDelta);} 

    fn bm<U>(&mut self, f: &mut FnMut() -> U, msg:String) -> U {
        
        let mut d = Duration::new(0,0);

        for i in 0..self.T {
            self.start();
            let ret = f();
            self.stop();
            d = d + self.curDelta;
        }
        d = d/self.T;
        println!("[Timing] {}: {:?}", msg, d);
        f()
    }

}

fn acc_ones(m:&Vec<bool>, acc:&mut Accumulator, hash: &PrimeHash) -> BigUint {
    //acc = acc.cleared(); 

    let mut prd = BigUint::one();
    for (i, bit) in (&m).iter().enumerate() {
        let prime = hash.get(i);
        if *bit {
            // B_j
            acc.add(&prime);
            prd *= prime;
        }
    }
    prd
}

fn acc_zeros(m:&Vec<bool>, acc:&mut Accumulator, hash: &PrimeHash) -> BigUint {
    //acc = acc.cleared(); 
    let mut prd = BigUint::one();

    for (i, bit) in (&m).iter().enumerate() {
        let prime = hash.get(i);
        if !*bit {
            // B_j
            acc.add(&prime);
            prd *= prime;
        }
    }
    prd
}

fn commit_bbf(m:&Vec<bool>, acc:&mut Accumulator, hash: &PrimeHash) {
    *acc = acc.cleared();
    acc_ones(m, acc, hash);
    //acc_ones(m, acc, hash);
}

fn commit_yy(m:&Vec<bool>, acc0:&mut Accumulator, acc1:&mut Accumulator, hash: &PrimeHash) {
    *acc0 = acc0.cleared();
    *acc1 = acc1.cleared();

    let prd1 =  acc_ones(m, acc1, hash);
    let prd0 = acc_zeros(m, acc0, hash);

    let whole_prd = prd0.clone()*prd1.clone();

    // XXX: Parameters are for testing purposes only
     let pi =
        proofs::ni_poprod_prove(
            &acc0.g,
            &acc0.g,
            &acc0.state(),
            &acc1.state(),
            &prd0,
            &prd1,
            &whole_prd,
            &acc0.n,
    );
}

// syntax: chunk_size, n_chunks, opn_size (in chunks)
static PRE_PARAMS: &'static [(usize, usize, usize)] = &[
    (256, 64, 16),
    (256, 128, 32),
    (256, 256, 64),
    (256, 512, 128),
     (256, 1024, 256),
    (256, 2048, 512),
    (256, 4096, 1024)
];


fn main() {

    const N:usize = 2048; // modulus size
    const L:usize = 128; // lambda
    const K:usize = 1;

    const SEED:[u8;32] = [2u8;32];

    const N_SAMPLES:u32 = 2;

    //let sz = 512;

    let mut rng = ChaChaRng::from_seed(SEED);
    let mut timer = ATimer::init(N_SAMPLES);

    // sz dependent code
    for (i,(chunk_sz, n_chunks, _)) in PRE_PARAMS.iter().enumerate()
    {

        let sz:usize = n_chunks * chunk_sz;
        let ph = Rc::new(PrimeHash::init(sz));
        

        // make data
        let mut vals: Vec<bool> = 
            (0..sz).map(|_| rng.gen()).collect();


        println!("-- N_CHUNKS = {}; CHUNK_SZ = {}; (SZ = {})--", 
            n_chunks, chunk_sz, sz);
        println!("#PRE-YY");
        {
            // init VC
            let config_yy = yinyan::Config { 
                lambda: L, k: K, n: N, precomp_l: *chunk_sz, size: sz, ph: ph.clone() };
            let mut vc_yy =
                yinyan::YinYanVectorCommitment::<Accumulator>::
                    setup::<RSAGroup, _>(&mut rng, &config_yy);

            let mut acc0 = vc_yy.accs[0].0.clone();
            let mut acc1 = vc_yy.accs[0].1.clone();

            //println!("Our acc's size: {}", acc0.int_size_bits);

            // commit
            /*
            timer.bm(
                &mut || { 
                    let c = commit_yy(&vals, &mut acc0, &mut acc1, &ph);
                    vc_yy.precompute(&vals);
                    c
                    }, 
                "Committing+Preproc YY".to_string()
            );
            */

            // prepare for opening
            println!("Committing and preprocessing...");
            vc_yy.precompute(&vals); 

            let openings = vec![1, 8, 64];
            for opn_sz in openings.iter()  {
                let chks_I:Vec<usize> = (0..*opn_sz).collect();

                let (flat_opn_vals, flat_opn_I) = 
                    yinyan::flatten_chunks(&vals, &chks_I, *chunk_sz);

                //let flat_opn_vals:Vec<bool> = I.iter().map( |i| vals[*i].clone() ).collect();
                let yy_opn_vals = 
                    yinyan::collect_chunks(&flat_opn_vals, &chks_I, *chunk_sz);

                // batch opening 
                timer.bm(
                    &mut || { vc_yy.batch_open_from_precomp(&yy_opn_vals, &chks_I) }, 
                    format!("OpeningFromPreProc YY {} (in bits = {})", opn_sz, opn_sz*chunk_sz).to_string()
                );
            }
/*
            // prepare for verification
            let pi = vc_yy.batch_open_from_precomp(&yy_opn_vals, &chks_I);


            // batch verify 
            timer.bm(
                &mut || { vc_yy.batch_verify_bits(0, &opn_vals, &I, &pi) }, 
                "Verify YY".to_string()
            );
            */
        }

        println!("");
    }
    

}
