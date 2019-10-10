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
    curDelta: Duration
}

impl ATimer {
    fn init() -> ATimer { ATimer {time: Instant::now(), curDelta: Instant::now().elapsed() } }
    fn start(&mut self) { self.time = Instant::now(); }
    fn stop(&mut self) { self.curDelta = self.time.elapsed(); }
    fn print(&self, msg:String) { println!("[Timing] {}: {:?}", msg, self.curDelta);} 

    fn bm<T>(&mut self, f: &Fn() -> T, msg:String) -> T {
        self.start();
        //let com = vc_bbf.commit(&vals);
        let ret = f();
        self.stop();
        self.print(msg);
        ret
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
    acc_ones(m, acc, hash);
    //acc_ones(m, acc, hash);
}

fn commit_yy(m:&Vec<bool>, acc0:&mut Accumulator, acc1:&mut Accumulator, hash: &PrimeHash) {
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



fn main() {

    const N:usize = 2048; // modulus size
    const L:usize = 128; // Not sure we are using it.
    const K:usize = 1;

    const SEED:[u8;32] = [2u8;32];

    let sz = 4096;

    let mut rng = ChaChaRng::from_seed(SEED);
    let ph = Rc::new(PrimeHash::init(sz));
    let mut timer = ATimer::init();

    // make data
    let mut vals: Vec<bool> = (0..sz).map(|_| rng.gen()).collect();

    {
        // init VC
        let config_yy = yinyan::Config { 
            lambda: L, k: K, n: N, precomp_l: 0, size: sz, ph: ph.clone() };
        let mut vc_yy =
            yinyan::YinYanVectorCommitment::<Accumulator>::
                setup::<RSAGroup, _>(&mut rng, &config_yy);

        let mut acc0 = vc_yy.accs[0].0.clone();
        let mut acc1 = vc_yy.accs[0].1.clone();

        println!("Our acc's size: {}", acc0.int_size_bits);

        // commit
        timer.start();
        //let com = vc_yy.commit_simple(&vals);
        commit_yy(&vals, &mut acc0, &mut acc1, &ph);
        timer.stop();
        timer.print("Committing YY".to_string());
    }

    {
        // init VC
        let config_bbf = binary::Config { lambda: L, n: N, ph: ph.clone() };
        let mut vc_bbf =
            binary::BinaryVectorCommitment::<Accumulator>::setup
                ::<RSAGroup, _>(&mut rng, &config_bbf);

        let acc = vc_bbf.acc.clone();
        println!("BBF acc's size: {}", acc.int_size_bits);


        // commit
        timer.start();
        let com = vc_bbf.commit(&vals);
        timer.stop();
        timer.print("Committing BBF".to_string());
    }

}
