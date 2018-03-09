use primal::{Primes};

const MAX_USIZE_PRIME : usize = 0;

fn close_prime(lower_bound: usize) -> usize {
    Primes::all().find(|p| lower_bound <= *p).unwrap_or(MAX_USIZE_PRIME)
}

pub struct Capacity {
    current: usize
}

impl Capacity {
    pub fn new(lower_bound: usize) -> Capacity {
        Capacity {
            current: close_prime(lower_bound)
        }
    }

    pub fn current(&self) -> usize {
        self.current
    }

        pub fn double(&mut self) {
        self.current = close_prime(2 * self.current)
    }
}
