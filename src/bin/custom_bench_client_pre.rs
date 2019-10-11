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


static NON_PRE_PARAMS: &'static [(usize,usize)] = &[
    (512, 64),
    (1024, 128),
    (2048, 256),
    (4096, 512),
    (8192, 1024),
    (16384, 2048),
    (32768, 4096),
    (65536, 8192),
    (131072, 16384)
];


fn main() {

    const N:usize = 2048; // modulus size
    const L:usize = 128; // lambda
    const K:usize = 1;

    const SEED:[u8;32] = [2u8;32];

    const N_SAMPLES:u32 = 3;

    //let sz = 512;

    let mut rng = ChaChaRng::from_seed(SEED);
    let mut timer = ATimer::init(N_SAMPLES);

    // sz dependent code
    for (i,(sz, opn_sz)) in NON_PRE_PARAMS.iter().enumerate()
    {

    let ph = Rc::new(PrimeHash::init(*sz));
    

    // make data
    let mut vals: Vec<bool> = (0..*sz).map(|_| rng.gen()).collect();
    let I:Vec<usize> = (0..*opn_sz).collect();
    let opn_vals:Vec<bool> = I.iter().map(|i| vals[*i].clone()).collect();

    println!("-- SZ = {}; OPN_SZ =  {} --", sz, opn_sz);
    println!("#YY");
    {
        // init VC
        let config_yy = yinyan::Config { 
            lambda: L, k: K, n: N, precomp_l: 0, size: *sz, ph: ph.clone() };
        let mut vc_yy =
            yinyan::YinYanVectorCommitment::<Accumulator>::
                setup::<RSAGroup, _>(&mut rng, &config_yy);

        let mut acc0 = vc_yy.accs[0].0.clone();
        let mut acc1 = vc_yy.accs[0].1.clone();

        //println!("Our acc's size: {}", acc0.int_size_bits);

        // commit
        timer.bm(
            &mut || { commit_yy(&vals, &mut acc0, &mut acc1, &ph) }, 
            "Committing YY".to_string()
        );

        // prepare for opening
        vc_yy.commit_simple(&vals); 


        // batch opening 
        timer.bm(
            &mut || { vc_yy.batch_open_bits(0, &opn_vals, &I) }, 
            "Opening YY".to_string()
        );

        // prepare for verification
        let pi = vc_yy.batch_open_bits(0, &opn_vals, &I);

        // batch verify 
        timer.bm(
            &mut || { vc_yy.batch_verify_bits(0, &opn_vals, &I, &pi) }, 
            "Verify YY".to_string()
        );
    }

    println!("#BBF");
    {
        // init VC
        let config_bbf = binary::Config { lambda: L, n: N, ph: ph.clone() };
        let mut vc_bbf =
            binary::BinaryVectorCommitment::<Accumulator>::setup
                ::<RSAGroup, _>(&mut rng, &config_bbf);

        let mut acc = vc_bbf.acc.clone();
        
        // commit
        timer.bm(
            &mut || { commit_bbf(&vals, &mut acc, &ph) }, 
            "Committing BBF".to_string()
        );

        // prepare for open
        vc_bbf.commit(&vals); 
       
        // batch opening 
        timer.bm(
            &mut || { vc_bbf.batch_open(&opn_vals, &I) }, 
            "Opening BBF".to_string()
        );

        // prepare for verification
        let pi = vc_bbf.batch_open(&opn_vals, &I);

        // batch verify 
        timer.bm(
            &mut || { vc_bbf.batch_verify(&opn_vals, &I, &pi) }, 
            "Verify BBF".to_string()
        );
    }
    println!("");
    }

}
