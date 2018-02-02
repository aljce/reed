#![allow(dead_code, unused_imports)]
#[macro_use]
extern crate quickcheck;
extern crate itertools;

mod arbitrary;

pub fn merge<A: Ord + Clone>(from: &mut [A], to: &mut [A], l: usize, m: usize, r: usize) {
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

pub fn copy_back<A: Clone>(from: &mut [A], to: &mut [A], l: usize, r: usize) {
    for k in l .. r {
        to[k] = from[k].clone();
    }
}

pub fn merge_sort<A>(a: &mut Vec<A>)
    where A: Ord + Default + Clone
{
    fn merge_sort_helper<A>(a: &mut [A], b: &mut [A], l: usize, r: usize)
        where A: Ord + Clone
    {
        if r - l > 1 {
            let m = (r + l) / 2;
            merge_sort_helper(a, b, l, m);
            merge_sort_helper(a, b, m, r);
            merge(a, b, l, m, r);
            copy_back(b, a, l, r);
        }
    }
    let len = a.len();
    let mut buf = vec![Default::default(); len];
    merge_sort_helper(a, &mut buf, 0, len);
}

#[cfg(test)]
mod tests {
    use std::hash::Hash;
    use std::collections::HashSet;
    use std::vec::Vec;

    use arbitrary::SortedVec;
    use super::*;

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
        let mut ys = vec![3, 7, 1];
        merge_sort(&mut ys);
        assert_eq!(ys, vec![1, 3, 7]);
    }

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

