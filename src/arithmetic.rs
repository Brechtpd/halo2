//! This module provides common utilities, traits and structures for group,
//! field and polynomial arithmetic.

use std::{env::var, time::Instant, mem::{size_of, self}};

use crate::plonk::{env_value, start_measure, stop_measure, self};

use super::multicore;
pub use ff::Field;
use group::{
    ff::{BatchInvert, PrimeField},
    Group as _, prime::PrimeCurveAffine,
};
use ark_std::{end_timer, start_timer, perf_trace::TimerInfo};

pub use pairing::arithmetic::*;

fn multiexp_serial<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C], acc: &mut C::Curve) {
    let coeffs: Vec<_> = coeffs.iter().map(|a| a.to_repr()).collect();

    let c = if bases.len() < 4 {
        1
    } else if bases.len() < 32 {
        3
    } else {
        (f64::from(bases.len() as u32)).ln().ceil() as usize
    };

    //println!("c: {}", c);

    fn get_at<F: PrimeField>(segment: usize, c: usize, bytes: &F::Repr) -> usize {
        let skip_bits = segment * c;
        let skip_bytes = skip_bits / 8;

        if skip_bytes >= 32 {
            return 0;
        }

        let mut v = [0; 8];
        for (v, o) in v.iter_mut().zip(bytes.as_ref()[skip_bytes..].iter()) {
            *v = *o;
        }

        let mut tmp = u64::from_le_bytes(v);
        tmp >>= skip_bits - (skip_bytes * 8);
        tmp = tmp % (1 << c);

        tmp as usize
    }

    let segments = (256 / c) + 1;

    #[derive(Clone, Copy)]
    enum Bucket<C: CurveAffine> {
        None,
        Affine(C),
        Projective(C::Curve),
    }

    impl<C: CurveAffine> Bucket<C> {
        fn add_assign(&mut self, other: &C) {
            *self = match *self {
                Bucket::None => Bucket::Affine(*other),
                Bucket::Affine(a) => Bucket::Projective(a + *other),
                Bucket::Projective(mut a) => {
                    a += *other;
                    Bucket::Projective(a)
                }
            }
        }

        fn add(self, mut other: C::Curve) -> C::Curve {
            match self {
                Bucket::None => other,
                Bucket::Affine(a) => {
                    other += a;
                    other
                }
                Bucket::Projective(a) => other + &a,
            }
        }
    }

    for current_segment in (0..segments).rev() {
        for _ in 0..c {
            *acc = acc.double();
        }

        let mut buckets: Vec<Bucket<C>> = vec![Bucket::None; (1 << c) - 1];

        for (coeff, base) in coeffs.iter().zip(bases.iter()) {
            let coeff = get_at::<C::Scalar>(current_segment, c, coeff);
            if coeff != 0 {
                buckets[coeff - 1].add_assign(base);
            }
        }

        // Summation by parts
        // e.g. 3a + 2b + 1c = a +
        //                    (a) + b +
        //                    ((a) + b) + c
        let mut running_sum = C::Curve::identity();
        for exp in buckets.into_iter().rev() {
            running_sum = exp.add(running_sum);
            *acc = *acc + &running_sum;
        }
    }
}

/// Performs a small multi-exponentiation operation.
/// Uses the double-and-add algorithm with doublings shared across points.
pub fn small_multiexp<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    //let start = start_timer!(|| "small_multiexp");

    let coeffs: Vec<_> = coeffs.iter().map(|a| a.to_repr()).collect();
    let mut acc = C::Curve::identity();

    // for byte idx
    for byte_idx in (0..32).rev() {
        // for bit idx
        for bit_idx in (0..8).rev() {
            acc = acc.double();
            // for each coeff
            for coeff_idx in 0..coeffs.len() {
                let byte = coeffs[coeff_idx].as_ref()[byte_idx];
                if ((byte >> bit_idx) & 1) != 0 {
                    acc += bases[coeff_idx];
                }
            }
        }
    }

    //end_timer!(start);

    acc
}

/// TEMP
pub static mut MULTIEXP_TOTAL_TIME: usize = 0;

/// Performs a multi-exponentiation operation.
///
/// This function will panic if coeffs and bases have a different length.
///
/// This will use multithreading if beneficial.
pub fn best_multiexp<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());

    /*let zero = C::Scalar::zero();
    let one = C::Scalar::one();
    let mut count_zero = 0usize;
    let mut count_one = 0usize;
    for coeff in coeffs {
        if *coeff == zero {
            count_zero += 1;
        } else if *coeff == one {
            count_one += 1;
        }
    }
    println!("size: {}, zeros: {}, ones: {}", coeffs.len(), count_zero, count_one);*/

    let num_threads = multicore::current_num_threads();
    let start = start_measure(format!("best multiexp {} ({})", coeffs.len(), num_threads), false);
    if coeffs.len() > num_threads {
        let chunk = coeffs.len() / num_threads;
        let num_chunks = coeffs.chunks(chunk).len();
        let mut results = vec![C::Curve::identity(); num_chunks];
        multicore::scope(|scope| {
            let chunk = coeffs.len() / num_threads;

            for ((coeffs, bases), acc) in coeffs
                .chunks(chunk)
                .zip(bases.chunks(chunk))
                .zip(results.iter_mut())
            {
                scope.spawn(move |_| {
                    multiexp_serial(coeffs, bases, acc);
                });
            }
        });
        let res = results.iter().fold(C::Curve::identity(), |a, b| a + b);
        let duration = stop_measure(start);

        #[allow(unsafe_code)]
        unsafe {
            MULTIEXP_TOTAL_TIME += duration;
        }

        res
    } else {
        let mut acc = C::Curve::identity();
        multiexp_serial(coeffs, bases, &mut acc);
        let duration = stop_measure(start);

        #[allow(unsafe_code)]
        unsafe {
            MULTIEXP_TOTAL_TIME += duration;
        }

        acc
    }
}

fn prefetch_range<const STRATEGY: i32>(start: *const i8, len: usize, prefetch_stride: usize)
{
    use core::arch::x86_64::_mm_prefetch;
    use ark_std::arch::x86_64::{_MM_HINT_T0, _MM_HINT_T1, _MM_HINT_T2/*, _MM_HINT_ET0*/};

    #[allow(unsafe_code)]
    unsafe {
        for offset in (0..len).step_by(prefetch_stride) {
            _mm_prefetch(start.offset(offset as isize), STRATEGY);
        }
    }
}


fn prefetch_multiexp_serial<C: CurveAffine, const PREFETCH: bool, const STRATEGY: i32>(coeffs: &[<C::Scalar as PrimeField>::Repr], bases: &[C], settings: &MultiExpSettings, segment: usize, acc: &mut C::Curve) {
    let c = settings.c;
    let lookahead = settings.prefetch_lookahead;
    let stride = settings.prefetch_stride;

    fn get_at<F: PrimeField>(segment: usize, c: usize, bytes: &F::Repr) -> usize {
        let skip_bits = segment * c;
        let skip_bytes = skip_bits / 8;

        if skip_bytes >= 32 {
            return 0;
        }

        let mut v = [0; 8];
        for (v, o) in v.iter_mut().zip(bytes.as_ref()[skip_bytes..].iter()) {
            *v = *o;
        }

        let mut tmp = u64::from_le_bytes(v);
        tmp >>= skip_bits - (skip_bytes * 8);
        tmp = tmp % (1 << c);

        tmp as usize
    }

    #[derive(Clone, Copy)]
    enum Bucket<C: CurveAffine> {
        None,
        Affine(C),
        Projective(C::Curve),
    }

    impl<C: CurveAffine> Bucket<C> {
        fn add_assign(&mut self, other: &C) {
            *self = match *self {
                Bucket::None => Bucket::Affine(*other),
                Bucket::Affine(a) => Bucket::Projective(a + *other),
                Bucket::Projective(mut a) => {
                    a += *other;
                    Bucket::Projective(a)
                }
            }
        }

        fn add(self, mut other: C::Curve) -> C::Curve {
            match self {
                Bucket::None => other,
                Bucket::Affine(a) => {
                    other += a;
                    other
                }
                Bucket::Projective(a) => other + &a,
            }
        }
    }

    let mut buckets: Vec<Bucket<C>> = vec![Bucket::None; (1 << c) - 1];

    for (idx, (coeff, base)) in coeffs.iter().zip(bases.iter()).enumerate() {
        // prefetch
        if PREFETCH {
            //println!("size: {}", mem::size_of::<C>() + 4);
            if idx + lookahead < coeffs.len() {
                let coeff = get_at::<C::Scalar>(segment, c, &coeffs[idx + lookahead]);
                if coeff != 0 {
                    #[allow(unsafe_code)]
                    unsafe {
                        prefetch_range::<STRATEGY>(
                            buckets.as_ptr().offset((coeff - 1) as isize) as *const i8,
                            mem::size_of::<C>() + 4,
                            stride,
                        );
                        //let ptr = &buckets[coeff] as *const i8;
                        //_mm_prefetch(buckets.as_ptr().offset(coeff as isize) as *const i8, _MM_HINT_T0)
                    }
                }
            }
        }
        let coeff = get_at::<C::Scalar>(segment, c, coeff);
        if coeff != 0 {
            buckets[coeff - 1].add_assign(base);
        }
    }

    // Summation by parts
    // e.g. 3a + 2b + 1c = a +
    //                    (a) + b +
    //                    ((a) + b) + c
    let mut running_sum = C::Curve::identity();
    for exp in buckets.into_iter().rev() {
        running_sum = exp.add(running_sum);
        *acc = *acc + &running_sum;
    }
}

/// Settings
#[derive(Debug)]
pub struct MultiExpSettings {
    c: usize,
    prefetch: bool,
    prefetch_lookahead: usize,
    prefetch_stride: usize,
    prefetch_strategy: i32,
}

/// Performs a multi-exponentiation operation.
///
/// This function will panic if coeffs and bases have a different length.
///
/// This will use multithreading if beneficial.
pub fn prefetch_multiexp<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C], settings: &MultiExpSettings) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    let num_threads = multicore::current_num_threads();

    let start = start_measure(format!("exponents to_repr {} ({})", coeffs.len(), num_threads), false);
    // Coeffs
    //let coeffs: Vec<_> = coeffs.iter().map(|a| a.to_repr()).collect();
    let mut exponents: Vec<_> = vec![C::Scalar::zero().to_repr(); coeffs.len()];
    for idx in 0..exponents.len() {
        exponents[idx] = coeffs[idx].to_repr();
    }
    stop_measure(start);

    let exps = &exponents.clone();

    let zero = C::Scalar::zero();
    let one = C::Scalar::one();
    let mut count_zero = 0usize;
    let mut count_one = 0usize;
    for coeff in coeffs {
        if *coeff == zero {
            count_zero += 1;
        } else if *coeff == one {
            count_one += 1;
        }
    }
    println!("size: {}, zeros: {}, ones: {}", coeffs.len(), count_zero, count_one);

    /*parallelize(&mut exponents, |coeffs, start| {
        for (exponent, coeff) in exponents.iter_mut().zip(coeffs[start..start+exponents.len()].iter()) {
            *exponent = coeff.to_repr();
        }
    });*/

    let start = start_measure(format!("prefetch multiexp {} ({}) {:?}", coeffs.len(), num_threads, settings), false);
    if coeffs.len() > num_threads {
        let num_chunks = (254 + settings.c - 1) / settings.c;
        println!("num_chunks: {}", num_chunks);
        let mut partials = vec![C::Curve::identity(); num_chunks];
        multicore::scope(|scope| {
            for (k, acc) in partials.iter_mut().enumerate() {
                scope.spawn(move |_| {
                    if settings.prefetch {
                        match settings.prefetch_strategy {
                            0 => prefetch_multiexp_serial::<C,true,0>(exps, bases, settings, k, acc),
                            1 => prefetch_multiexp_serial::<C,true,1>(exps, bases, settings, k, acc),
                            2 => prefetch_multiexp_serial::<C,true,2>(exps, bases, settings, k, acc),
                            3 => prefetch_multiexp_serial::<C,true,3>(exps, bases, settings, k, acc),
                            4 => prefetch_multiexp_serial::<C,true,4>(exps, bases, settings, k, acc),
                            5 => prefetch_multiexp_serial::<C,true,5>(exps, bases, settings, k, acc),
                            6 => prefetch_multiexp_serial::<C,true,6>(exps, bases, settings, k, acc),
                            7 => prefetch_multiexp_serial::<C,true,7>(exps, bases, settings, k, acc),
                            _ => unimplemented!()
                        }
                    } else {
                        prefetch_multiexp_serial::<C,false,0>(exps, bases, settings, k, acc);
                    }
                });
            }
        });

        let mut res = partials[num_chunks - 1];
        for i in (0..=num_chunks - 2).rev() {
            for _ in 0..settings.c {
                res = res.double();
            }
            res = res + partials[i];
        }

        stop_measure(start);
        res
    } else {
        let mut acc = C::Curve::identity();
        multiexp_serial(coeffs, bases, &mut acc);
        stop_measure(start);
        acc
    }
}

/// Performs a radix-$2$ Fast-Fourier Transformation (FFT) on a vector of size
/// $n = 2^k$, when provided `log_n` = $k$ and an element of multiplicative
/// order $n$ called `omega` ($\omega$). The result is that the vector `a`, when
/// interpreted as the coefficients of a polynomial of degree $n - 1$, is
/// transformed into the evaluations of this polynomial at each of the $n$
/// distinct powers of $\omega$. This transformation is invertible by providing
/// $\omega^{-1}$ in place of $\omega$ and dividing each resulting field element
/// by $n$.
///
/// This will use multithreading if beneficial.
pub fn best_fft<G: Group>(a: &mut [G], omega: G::Scalar, log_n: u32) {
    let threads = multicore::current_num_threads();
    let log_threads = log2_floor(threads);

    let start = start_measure(format!("best_fft {} ({})", a.len(), threads), false);
    if log_n <= log_threads {
        serial_fft(a, omega, log_n);
    } else {
        parallel_fft(a, omega, log_n, log_threads);
    }
    stop_measure(start);
}

fn serial_fft<G: Group>(a: &mut [G], omega: G::Scalar, log_n: u32) {
    fn bitreverse(mut n: u32, l: u32) -> u32 {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }

    let n = a.len() as u32;
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n);
        if k < rk {
            a.swap(rk as usize, k as usize);
        }
    }

    let mut m = 1;
    for _ in 0..log_n {
        let w_m = omega.pow_vartime(&[u64::from(n / (2 * m)), 0, 0, 0]);

        let mut k = 0;
        while k < n {
            let mut w = G::Scalar::one();
            for j in 0..m {
                let mut t = a[(k + j + m) as usize];
                t.group_scale(&w);
                a[(k + j + m) as usize] = a[(k + j) as usize];
                a[(k + j + m) as usize].group_sub(&t);
                a[(k + j) as usize].group_add(&t);
                w *= &w_m;
            }

            k += 2 * m;
        }

        m *= 2;
    }
}

fn parallel_fft<G: Group>(a: &mut [G], omega: G::Scalar, log_n: u32, log_threads: u32) {
    assert!(log_n >= log_threads);

    let num_threads = 1 << log_threads;
    let log_new_n = log_n - log_threads;
    let mut tmp = vec![vec![G::group_zero(); 1 << log_new_n]; num_threads];
    let new_omega = omega.pow_vartime(&[num_threads as u64, 0, 0, 0]);

    multicore::scope(|scope| {
        let a = &*a;

        for (j, tmp) in tmp.iter_mut().enumerate() {
            scope.spawn(move |_| {
                // Shuffle into a sub-FFT
                let omega_j = omega.pow_vartime(&[j as u64, 0, 0, 0]);
                let omega_step = omega.pow_vartime(&[(j as u64) << log_new_n, 0, 0, 0]);

                let mut elt = G::Scalar::one();

                for (i, tmp) in tmp.iter_mut().enumerate() {
                    for s in 0..num_threads {
                        let idx = (i + (s << log_new_n)) % (1 << log_n);
                        let mut t = a[idx];
                        t.group_scale(&elt);
                        tmp.group_add(&t);
                        elt *= &omega_step;
                    }
                    elt *= &omega_j;
                }

                // Perform sub-FFT
                serial_fft(tmp, new_omega, log_new_n);
            });
        }
    });

    // Unshuffle
    let mask = (1 << log_threads) - 1;
    for (idx, a) in a.iter_mut().enumerate() {
        *a = tmp[idx & mask][idx >> log_threads];
    }
}

/// This evaluates a provided polynomial (in coefficient form) at `point`.
pub fn eval_polynomial<F: Field>(poly: &[F], point: F) -> F {
    let n = poly.len();
    let num_threads = multicore::current_num_threads();
    let mut chunk = (n as usize) / num_threads;
    if chunk < num_threads {
        chunk = n as usize;
    }

    let mut parts = vec![F::zero(); num_threads];
    multicore::scope(|scope| {
        for (chunk_num, (out, poly)) in
            parts.chunks_mut(1)
            .zip(poly.chunks(chunk))
            .enumerate() {
            scope.spawn(move |_| {
                let start = chunk_num * chunk;
                out[0] = poly.iter().rev().fold(F::zero(), |acc, coeff| acc * point + coeff)
                    * point.pow_vartime(&[start as u64, 0, 0, 0]);
            });
        }
    });

    parts.iter().fold(F::zero(), |acc, coeff| acc + coeff)
}

/// This computes the inner product of two vectors `a` and `b`.
///
/// This function will panic if the two vectors are not the same size.
pub fn compute_inner_product<F: Field>(a: &[F], b: &[F]) -> F {
    // TODO: parallelize?
    assert_eq!(a.len(), b.len());

    let mut acc = F::zero();
    for (a, b) in a.iter().zip(b.iter()) {
        acc += (*a) * (*b);
    }

    acc
}

/// Divides polynomial `a` in `X` by `X - b` with
/// no remainder.
pub fn kate_division<'a, F: Field, I: IntoIterator<Item = &'a F>>(a: I, mut b: F) -> Vec<F>
where
    I::IntoIter: DoubleEndedIterator + ExactSizeIterator,
{
    b = -b;
    let a = a.into_iter();

    let mut q = vec![F::zero(); a.len() - 1];

    let mut tmp = F::zero();
    for (q, r) in q.iter_mut().rev().zip(a.rev()) {
        let mut lead_coeff = *r;
        lead_coeff.sub_assign(&tmp);
        *q = lead_coeff;
        tmp = lead_coeff;
        tmp.mul_assign(&b);
    }

    q
}

/// This simple utility function will parallelize an operation that is to be
/// performed over a mutable slice.
pub fn parallelize<T: Send, F: Fn(&mut [T], usize) + Send + Sync + Clone>(v: &mut [T], f: F) {
    let n = v.len();
    let num_threads = multicore::current_num_threads();
    let mut chunk = (n as usize) / num_threads;
    if chunk < num_threads {
        chunk = n as usize;
    }

    multicore::scope(|scope| {
        for (chunk_num, v) in v.chunks_mut(chunk).enumerate() {
            let f = f.clone();
            scope.spawn(move |_| {
                let start = chunk_num * chunk;
                f(v, start);
            });
        }
    });
}

/// This simple utility function will parallelize an operation that is to be
/// performed over a mutable slice.
pub fn parallelize_count<T: Send, F: Fn(&mut [T], usize) + Send + Sync + Clone>(v: &mut [T], num_threads: usize, f: F) {
    let n = v.len();
    let mut chunk = (n as usize) / num_threads;
    if chunk < num_threads {
        chunk = n as usize;
    }

    multicore::scope(|scope| {
        for (chunk_num, v) in v.chunks_mut(chunk).enumerate() {
            let f = f.clone();
            scope.spawn(move |_| {
                f(v, chunk_num);
            });
        }
    });
}

fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow + 1)) <= num {
        pow += 1;
    }

    pow
}

/// Returns coefficients of an n - 1 degree polynomial given a set of n points
/// and their evaluations. This function will panic if two values in `points`
/// are the same.
pub fn lagrange_interpolate<F: FieldExt>(points: &[F], evals: &[F]) -> Vec<F> {
    assert_eq!(points.len(), evals.len());
    if points.len() == 1 {
        // Constant polynomial
        return vec![evals[0]];
    } else {
        let mut denoms = Vec::with_capacity(points.len());
        for (j, x_j) in points.iter().enumerate() {
            let mut denom = Vec::with_capacity(points.len() - 1);
            for x_k in points
                .iter()
                .enumerate()
                .filter(|&(k, _)| k != j)
                .map(|a| a.1)
            {
                denom.push(*x_j - x_k);
            }
            denoms.push(denom);
        }
        // Compute (x_j - x_k)^(-1) for each j != i
        denoms.iter_mut().flat_map(|v| v.iter_mut()).batch_invert();

        let mut final_poly = vec![F::zero(); points.len()];
        for (j, (denoms, eval)) in denoms.into_iter().zip(evals.iter()).enumerate() {
            let mut tmp: Vec<F> = Vec::with_capacity(points.len());
            let mut product = Vec::with_capacity(points.len() - 1);
            tmp.push(F::one());
            for (x_k, denom) in points
                .iter()
                .enumerate()
                .filter(|&(k, _)| k != j)
                .map(|a| a.1)
                .zip(denoms.into_iter())
            {
                product.resize(tmp.len() + 1, F::zero());
                for ((a, b), product) in tmp
                    .iter()
                    .chain(std::iter::once(&F::zero()))
                    .zip(std::iter::once(&F::zero()).chain(tmp.iter()))
                    .zip(product.iter_mut())
                {
                    *product = *a * (-denom * x_k) + *b * denom;
                }
                std::mem::swap(&mut tmp, &mut product);
            }
            assert_eq!(tmp.len(), points.len());
            assert_eq!(product.len(), points.len() - 1);
            for (final_coeff, interpolation_coeff) in final_poly.iter_mut().zip(tmp.into_iter()) {
                *final_coeff += interpolation_coeff * eval;
            }
        }
        final_poly
    }
}

#[cfg(test)]
use pairing::bn256::Fr as Fp;
use pairing::bn256 as bn256;

#[test]
fn test_lagrange_interpolate() {
    let points = (0..5).map(|_| Fp::rand()).collect::<Vec<_>>();
    let evals = (0..5).map(|_| Fp::rand()).collect::<Vec<_>>();

    for coeffs in 0..5 {
        let points = &points[0..coeffs];
        let evals = &evals[0..coeffs];

        let poly = lagrange_interpolate(points, evals);
        assert_eq!(poly.len(), points.len());

        for (point, eval) in points.iter().zip(evals) {
            assert_eq!(eval_polynomial(&poly, *point), *eval);
        }
    }
}

#[test]
fn test_multiexp() {
    let n = 1 << env_value("K", 16);

    let c = env_value("C", 16);
    let prefetch = env_value("PREFETCH", 1) != 0;
    let prefetch_lookahead = env_value("look", 1);
    let prefetch_stride = env_value("stride", 16);
    let prefetch_strategy = env_value("strategy", 7) as i32;

    let mut settings = MultiExpSettings {
        c,
        prefetch,
        prefetch_lookahead,
        prefetch_stride,
        prefetch_strategy,
    };

    let mut coeffs = vec![Fp::zero(); n];
    for i in 0..n {
        coeffs[i] = Fp::rand();
    }

    let rng = &mut rand::thread_rng();
    let bases = vec![pairing::bn256::G1Affine::random(rng); n];

    /*let res_a = best_multiexp(&coeffs, &bases);

    let res_b = prefetch_multiexp(&coeffs, &bases, &settings);

    assert_eq!(res_a, res_b);*/

    settings.prefetch = false;
    let res_a = prefetch_multiexp(&coeffs, &bases, &settings);

    for lookahead in 1..=4 {
        for stride in [16usize].iter() {
            for strategy in 0..=7 {
                settings.prefetch = true;
                settings.prefetch_lookahead = lookahead;
                settings.prefetch_stride = *stride;
                settings.prefetch_strategy = strategy;
                let res_b = prefetch_multiexp(&coeffs, &bases, &settings);
                assert_eq!(res_a, res_b);
            }
        }
    }
}

