extern crate accumulators;
extern crate rand_chacha;

use num_bigint::{IntoBigUint};
use num_traits::{One, Zero};

use std::{thread, time};


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
use accumulators::traits::*;


//use super::*;
use accumulators::PrimeHash;
use accumulators::group::RSAGroup;
use accumulators::traits::{BatchedAccumulator, StaticAccumulator, StaticVectorCommitment};
use accumulators::Accumulator;
use accumulators::vc::{binary, yinyan};
use accumulators::proofs;
use num_bigint::{BigInt, BigUint, RandPrime, RandBigInt};
use rand::{Rng, SeedableRng};
use crate::rand_chacha::ChaChaRng;

use std::time::{Duration, Instant};

struct ATimer {
    time: Instant,
    curDelta: Duration,
    T: u32, // number of iterations
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

    fn bm_pre<T,U>(&mut self, pre_f: &mut FnMut() -> T, f: &mut FnMut(T) -> U, msg:String) -> U {
        
        let mut d = Duration::new(0,0);

        for i in 0..self.T {
            let setup = pre_f();
            self.start();
            let ret = f(setup);
            self.stop();
            d = d + self.curDelta;
        }
        d = d/self.T;
        println!("[Timing] {}: {:?}", msg, d);
        f(pre_f())
    }

}


fn main() {

    const N:usize = 2048; // modulus size
    const L:usize = 256; // exponent size 


    const SEED:[u8;32] = [2u8;32];
  
    const N_SAMPLES:u32 = 30;

    //let mut results = Vec::with_capacity(N_SAMPLES as usize);

    //let sz = 512;

    let mut rng = ChaChaRng::from_seed(SEED);
    let mut timer = ATimer::init(N_SAMPLES);



    let mut pre_fun = || -> (_,_, _) {
        let (modulus, g) = RSAGroup::generate_primes(&mut rng, N).unwrap();
        let p = rng.gen_biguint(L);
        let r = rng.gen_biguint(N);
        let g1 = g.modpow(&r, &modulus);
        (p, modulus, g1)
    };

    let ten_millis = time::Duration::from_millis(10);


    let mut fun = |(p,g, modulus):(BigUint, BigUint, BigUint)| -> BigUint {
        let x = g.modpow(&p, &modulus);
        //results.push(x.clone());
        x
    };

    let bm_res = timer.bm_pre(&mut pre_fun, &mut fun, "Exp".to_string());


}
