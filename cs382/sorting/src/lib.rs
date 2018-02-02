#![allow(dead_code, unused_imports)]
#[macro_use]
extern crate quickcheck;
extern crate itertools;
extern crate num_iter;

/// Iterative Merge Sort
/// ©2017 Kyle McKean
/// https://github.com/mckeankylej/reed/cs382/sorting

use num_iter::{range_step};

mod arbitrary;

fn merge<A: Ord + Clone>(from: &mut [A], to: &mut [A], l: usize, m: usize, r: usize) {
    let mut i = l;
    let mut j = m;
    for k in l .. r {
        if i < m && (j >= r || from[i] <= from[j]) {
            to[k] = from[i].clone();
            i += 1;
        } else {
            to[k] = from[j].clone();
            j += 1;
        }
    }
}

fn copy_back<A: Clone>(from: &mut [A], to: &mut [A]) {
    to.clone_from_slice(from);
}

fn lg(x: usize) -> usize {
    // There is never enough bit twiddling in this world
    let bit_size = 0usize.count_zeros() - 1;
    (bit_size - x.leading_zeros()) as usize
}

use std::fmt::Debug;

pub fn merge_sort<A>(a: &mut Vec<A>)
    where A: Ord + Default + Clone
{
    let n = a.len();
    let mut b = vec![Default::default(); n];
    for i in 1 .. lg(n) + 1 {
        for j in range_step(0, n - 2 * i, 2 * i) {
            merge(a, &mut b, j, j + i, j + 2 * i);
        }
        merge(a, &mut b, n - 2 * i, n - i, n);
        copy_back(&mut b, a)
    }
}

#[cfg(test)]
mod tests {
    use std::hash::Hash;
    use std::collections::HashSet;
    use std::vec::Vec;

    use arbitrary::SortedVec;
    use super::*;

    #[test]
    fn lg_unit() {
        assert_eq!(3, lg(8));
        assert_eq!(4, lg(16));
        assert_eq!(3, lg(9));
    }
    #[test]
    fn lg_power_identity() {
        quickcheck! {
            fn prop(x: usize) -> bool {
                let power = 2 ^ x;
                0 < power && lg(power) == x
            }
        }
    }

    fn is_ascending<A: Ord>(vec: &Vec<A>) -> bool {
        // TODO: O(n^2) check rewrite to use a hashset
        vec.iter().enumerate().all(|(i, v)| {
            (&vec[i .. vec.len()]).iter().all(|x| v <= x)
        })
    }

    fn is_permutation<A: Eq + Hash>(before: Vec<A>, after: Vec<A>) -> bool {
        let elems_before = before.into_iter().collect::<HashSet<A>>();
        let elems_after = after.into_iter().collect::<HashSet<A>>();
        elems_before == elems_after
    }

    #[test]
    fn merge_unit() {
        let mut ys = vec![5, 7, 2, 9];
        let mut buf = vec![0, 0, 0, 0];
        merge(&mut ys, &mut buf, 0, 2, 4);
        ys.sort();
        assert_eq!(ys, buf);
    }

    fn merge_sorted_vec<A>(sorted_xs: SortedVec<A>, sorted_ys: SortedVec<A>) -> Vec<A>
        where A: Ord + Default + Clone
    {
        let mut xs = sorted_xs.sorted_vec;
        let mut ys = sorted_ys.sorted_vec;
        let xs_len = xs.len();
        let ys_len = ys.len();
        let total_len = xs_len + ys_len;
        xs.append(&mut ys);
        let mut buf = vec![Default::default(); total_len];
        merge(&mut xs, &mut buf, 0, xs_len, total_len);
        buf
    }

    /// This test uses [quickcheck](https://github.com/BurntSushi/quickcheck) to randomly test
    /// a property.
    /// There are two conditions a sorting algorithm must follow.
    /// After sorting the array must be
    /// - in ascending order
    /// - a permutation of the original array
    /// These properties are randomly tested for the merge function and the merge_sort function.
    /// This property uses a type defined in `arbitrary` to ensure the random vectors are in
    /// sorted order called `SortedVec`.
    #[test]
    fn merge_ascending() {
        quickcheck! {
            fn prop(sorted_xs: SortedVec<i32>, sorted_ys: SortedVec<i32>) -> bool {
                let res = merge_sorted_vec(sorted_xs, sorted_ys);
                is_ascending(&res)
            }
        }
    }

    #[test]
    fn merge_permutation() {
        quickcheck! {
            fn prop(sorted_xs: SortedVec<i32>, sorted_ys: SortedVec<i32>) -> bool {
                let mut xs = sorted_xs.sorted_vec.clone();
                let mut ys = sorted_ys.sorted_vec.clone();
                xs.append(&mut ys);
                let res = merge_sorted_vec(sorted_xs, sorted_ys);
                is_permutation(res, xs)
            }
        }

    }

    #[test]
    fn merge_sort_unit() {
        let mut ys = vec![3, 2, 7, 1];
        merge_sort(&mut ys);
        assert_eq!(ys, vec![1, 2, 3, 7]);
    }

    /// The following two tests ''prove'' that merge_sort is correct ''for all'' vectors
    #[test]
    fn merge_sort_ascending() {
        quickcheck! {
            fn prop(xs: Vec<i32>) -> bool {
                let mut ys = xs.clone();
                merge_sort(&mut ys);
                is_ascending(&ys)
            }
        }
    }

    #[test]
    fn merge_sort_permutation() {
        quickcheck! {
            fn prop(xs: Vec<i32>) -> bool {
                let mut ys = xs.clone();
                merge_sort(&mut ys);
                is_permutation(xs, ys)
            }
        }
    }
}

