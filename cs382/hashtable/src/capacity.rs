use primal::{Primes};

pub fn close_prime(lower_bound: usize) -> usize {
    const MAX_USIZE_PRIME : usize = 0xFFFFFFFFFFFFFFC5;
    Primes::all().find(|p| lower_bound <= *p).unwrap_or(MAX_USIZE_PRIME)
}
