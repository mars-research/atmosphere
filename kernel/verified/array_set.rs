use vstd::prelude::*;
verus! {
use crate::array::Array;
use vstd::set_lib::*;


/// A set of intergers from 0 to N - 1.
pub struct ArraySet<const N: usize> {
    pub data: Array<bool, N>,
    pub len: usize,

    pub set: Ghost<Set<usize>>,
}

impl <const N: usize> ArraySet<N> {

    pub fn new() -> (ret:Self)
        ensures
            ret.wf(),
            ret@ == Set::<usize>::empty(),
    {
        let mut ret = Self{
            data: Array::new(),
            len: 0,
            set:Ghost(Set::<usize>::empty()),
        };
        for i in 0..N
            invariant
                0<=i<=N,
                ret.data.wf(),
                ret.len == 0,
                ret.set@ == Set::<usize>::empty(),
                forall|j:int|
                    0<=j<i ==> ret.data@[j] == false,
        {
            ret.data.set(i,false);
        }
        ret
    }

    pub fn init(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ == Set::<usize>::empty(),
    {
            self.len = 0;
            self.set = Ghost(Set::<usize>::empty());
        for i in 0..N
            invariant
                0<=i<=N,
                self.data.wf(),
                self.len == 0,
                self.set@ == Set::<usize>::empty(),
                forall|j:int|
                    0<=j<i ==> self.data@[j] == false,
        {
            self.data.set(i,false);
        }
    }

    pub closed spec fn view(&self) -> Set<usize>{
        self.set@
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret:usize)
        requires
            self.wf(),
        ensures
            ret == self.set@.len(),
    {
        self.len
    }

    pub closed spec fn spec_len(&self) -> usize{
        self.set@.len() as usize
    }

    pub closed spec fn wf(&self) -> bool{
        &&&
        self.data.wf()
        &&&
        self.set@.finite()
        &&&
        0 <= self.len <= N
        &&&
        forall|i:usize| 
            #![trigger self.data@[i as int]]
            #![trigger self.set@.contains(i)]
            0 <= i < N && self.data@[i as int] ==> self.set@.contains(i)
        &&&
        forall|i:usize| 
            #![trigger self.data@[i as int]]
            #![trigger self.set@.contains(i)]
            self.set@.contains(i) ==> 0 <= i < N && self.data@[i as int]     
        &&&
        self.len == self.set@.len() 
    }

    pub fn insert(&mut self, v:usize)
        requires
            old(self).wf(),
            old(self)@.contains(v) == false,
            0 <= v < N,
        ensures
            self.wf(),
            self@ == old(self)@.insert(v),
    {
        proof {
            // Prove that self.len < N using our helper lemma
            Self::lemma_set_missing_element_size(self.set@, v, N);
        }

        self.data.set(v, true);
        self.set = Ghost(self.set@.insert(v));
        self.len = self.len + 1;
    }

    pub fn remove(&mut self, v:usize)
        requires
            old(self).wf(),
            old(self)@.contains(v) == true,
        ensures
            self.wf(),
            self@ == old(self)@.remove(v),
    {
        self.data.set(v, false);
        self.len = self.len - 1;
        self.set = Ghost(self.set@.remove(v));
    }


    // Helper lemma: a finite set contained in [0, m) has at most m elements
    proof fn lemma_finite_set_bounded_size(s: Set<usize>, m: usize)
        requires
            s.finite(),
            forall|i: usize| #[trigger] s.contains(i) ==> 0 <= i < m,
        ensures
            s.len() <= m,
        decreases m,
    {
        if m == 0 {
            // s is contained in [0, 0) = empty set, so s is empty
            if s.len() > 0 {
                let elem = s.choose();
                assert(s.contains(elem));
                assert(false);
            }
        } else {
            // m > 0
            if s.len() == 0 {
            } else {
                // s is non-empty
                // split based on whether s contains m-1
                let m_minus_1 = (m - 1) as usize;

                if s.contains(m_minus_1) {
                    // m-1 is in s
                    let s_without_last = s.remove(m_minus_1);

                    // Recursively prove for s_without_last in [0, m-1)
                    Self::lemma_finite_set_bounded_size(s_without_last, m_minus_1);

                } else {
                    // m-1 is not in s
                    // So all elements of s are in [0, m-1)

                    // Recursively prove for s in [0, m-1)
                    Self::lemma_finite_set_bounded_size(s, m_minus_1);
                }
            }
        }
    }

        // Helper lemma: if a set contains only elements in [0, n), and doesn't contain a specific element v in [0, n),
    // then the set has strictly fewer than n elements
    proof fn lemma_set_missing_element_size(s: Set<usize>, v: usize, n: usize)
        requires
            s.finite(),
            forall|i: usize| #[trigger] s.contains(i) ==> 0 <= i < n,
            0 <= v < n,
            !s.contains(v),
            n > 0,
        ensures
            s.len() < n,
        decreases n,
    {
        if n == 1 {
            // n = 1, so the only possible element is 0
            // v must be 0, and s doesn't contain 0
            // Therefore s is empty and s.len() == 0 < 1
            if s.len() > 0 {
                let elem = s.choose();
                assert(s.contains(elem));
                assert(elem == 0);
                assert(false);
            }
        } else {
            // n > 1
            // Consider the set restricted to [0, n-1)
            let n_minus_1 = (n - 1) as usize;
            let s_restricted = s.filter(|i: usize| 0 <= i < n_minus_1);

            if v < n_minus_1 {
                // Recursively prove for n-1
                Self::lemma_set_missing_element_size(s_restricted, v, n_minus_1);

                // Now, s can have at most one more element than s_restricted (the element n-1)
                // So s.len() <= s_restricted.len() + 1 < (n-1) + 1 = n

                // Elements of s are either in s_restricted or equal to n-1
                let elem_n_minus_1 = n_minus_1;
                if s.contains(elem_n_minus_1) {
                    // s = s_restricted �~H� {n-1}
                    let s_without_last = s.remove(elem_n_minus_1);
                                        assert(s_without_last =~= s_restricted);
                } else {
                    // s = s_restricted
                    assert(s =~= s_restricted);
                }
            } else {
                // So s doesn't contain n_minus_1, and all elements of s are in [0, n)
                // Now s is entirely contained in [0, n_minus_1)
                // We need to prove s.len() < n, which is equivalent to s.len() <= n_minus_1

                // Use induction: if s is empty, done. Otherwise, pick an element, remove it, and recurse
                if s.len() == 0 {
                } else {
                    // s has at least one element
                    let w = s.choose();
                    assert(s.contains(w));
                    assert(0 <= w < n_minus_1);

                    if n_minus_1 == 0 {
                        // All elements of s are in [0, 0), which is empty
                        assert(s.len() == 0);
                    } else {
                        // Let's construct an upper bound proof:
                        // We'll remove one element at a time from s and show the count
                        let s_minus_w = s.remove(w);

                        // If s_minus_w is empty, then s has 1 element, so s.len() = 1 <= n_minus_1 (since n_minus_1 > 0)
                        if s_minus_w.len() == 0 {
                        } else {
                            // s_minus_w is non-empty
                            // I think I need a lemma that directly states: finite set in [0, m) has size <= m
                            // Let me extract that as a separate helper
                            Self::lemma_finite_set_bounded_size(s, n_minus_1);
                            assert(s.len() <= n_minus_1);
                        }
                    }
                }
            }
        }
    }
}

}
