use quickcheck::{Arbitrary, Gen};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SortedVec<A> {
    pub sorted_vec: Vec<A>
}

impl<A: Ord> SortedVec<A> {
    pub fn new(mut vec: Vec<A>) -> SortedVec<A> {
        vec.sort();
        SortedVec {
            sorted_vec: vec
        }
    }
}

impl<A: Arbitrary + Ord> Arbitrary for SortedVec<A> {
  fn arbitrary<G: Gen>(g: &mut G) -> SortedVec<A> {
      SortedVec::new(Arbitrary::arbitrary(g))
    }

    fn shrink(&self) -> Box<Iterator<Item=SortedVec<A>>> {
        let shrunk = self.sorted_vec.shrink();
        Box::new(shrunk.map(|vec1| {
            let mut vec2 = vec1.clone();
            vec2.sort();
            assert!(vec1 == vec2);
            SortedVec { sorted_vec: vec1 }
        }))
    }

}
