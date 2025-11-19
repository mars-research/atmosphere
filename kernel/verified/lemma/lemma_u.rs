use vstd::prelude::*;
verus! {

use crate::util::page_ptr_util_u::*;

pub broadcast proof fn map_equal_implies_submap_each_other<K, V>(a: Map<K, V>, b: Map<K, V>)
    requires
        a =~= b,
    ensures
        #[trigger] a.submap_of(b),
        b.submap_of(a),
{
}

pub broadcast proof fn submap_by_transitivity<K, V>(a: Map<K, V>, b: Map<K, V>, c: Map<K, V>)
    requires
        #[trigger] a.submap_of(b),
        #[trigger] b.submap_of(c),
    ensures
        a.submap_of(c),
{
    assert(forall|k: K|
        #![trigger a.dom().contains(k)]
        #![trigger b.dom().contains(k)]
        a.dom().contains(k) ==> b.dom().contains(k) && a[k] == b[k]);
}

pub proof fn page_ptr_valid_imply_MEM_valid(v: usize)
    requires
        page_ptr_valid(v),
    ensures
        MEM_valid(v),
{
    assert(v & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector)
        requires
            ((v % 4096) == 0) && ((v / 4096) < 2 * 1024 * 1024),
    ;
}

pub proof fn seq_push_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.contains(x) ==> s.push(v).contains(v) && s.push(v).contains(x),
        forall|s: Seq<A>, v: A| #![auto] s.push(v).contains(v),
        forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x ==> !s.push(v).contains(x),
{
    // Prove the first postcondition: if s contains x, then s.push(v) contains both v and x
    assert forall|s: Seq<A>, v: A, x: A| s.contains(x) implies s.push(v).contains(v) && s.push(v).contains(x) by {
        // If s contains x, there exists an index i where s[i] == x
        if s.contains(x) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
            // After push, s.push(v)[i] == s[i] == x (by axiom_seq_push_index_different)
            assert(s.push(v)[i] == x);
            // s.push(v) also contains v at index s.len()
            assert(s.push(v)[s.len() as int] == v); // by axiom_seq_push_index_same
        }
    };
    
    // Prove the second postcondition: s.push(v) always contains v
    assert forall|s: Seq<A>, v: A|  #![auto] s.push(v).contains(v) by {
        // v is at index s.len() in s.push(v)
        assert(s.push(v)[s.len() as int] == v); // by axiom_seq_push_index_same
    };
    
    // Prove the third postcondition: if s doesn't contain x and v != x, then s.push(v) doesn't contain x
    assert forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x implies !s.push(v).contains(x) by {
        if !s.contains(x) && v != x {
            // Proof by contradiction: assume s.push(v) contains x
            if s.push(v).contains(x) {
                // Then there exists an index j where s.push(v)[j] == x
                let j = choose|j: int| 0 <= j < s.push(v).len() && s.push(v)[j] == x;
                
                assert(false);
            }
        }
    };

}

pub proof fn seq_push_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.no_duplicates() && s.contains(v) && v != x
            ==> 
            s.push(x).index_of(v) == s.index_of(v),
{
    assert forall|s: Seq<A>, v: A, x: A| s.no_duplicates() && s.contains(v) && v != x implies s.push(x).index_of(v) == s.index_of(v) by {
        assert(s.push(x)[s.index_of(v)] == s[s.index_of(v)]);
    }
}

pub proof fn seq_skip_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A,|
            #![auto]
            s.len() != 0 && s.no_duplicates() && s.contains(v) && s[0] != v
            ==> 
            s.skip(1).index_of(v) == s.index_of(v) - 1,
{
    assert forall|s: Seq<A>, v: A| 
        #![auto] s.len() != 0 && s.no_duplicates() && s.contains(v) && s[0] != v
    implies
        s.skip(1).index_of(v) == s.index_of(v) - 1
    by {
        // Get the index where v appears in s
        let i = s.index_of(v);
        
        // Now we need to show that s.skip(1).index_of(v) == i - 1
        // We know s[i] == v and i > 0, so i-1 is a valid index in s.skip(1)
        assert(s.skip(1)[i - 1] == s[i]);
    }

}

pub proof fn seq_to_set_lemma<A>()
    ensures
        forall|s: Seq<A>, a: A|
            #![trigger s.contains(a)]
            #![trigger s.to_set().contains(a)]
            s.contains(a) == s.to_set().contains(a),
{
}

#[verifier(external_body)]
pub proof fn seq_pop_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int|
            s.no_duplicates() && 0 <= i < s.len() - 1 ==> s.drop_last().contains(s[s.len() - 1])
                && s.drop_last()[i] == s[i],
        forall|s: Seq<A>, v: A|
            s.no_duplicates() && s[s.len() - 1] == v ==> s.drop_last().to_set().contains(v)
                == false,
        forall|s: Seq<A>, v: A|
            s.no_duplicates() && s[s.len() - 1] != v ==> s.drop_last().to_set().contains(v)
                == s.to_set().contains(v),
{
}

pub proof fn seq_update_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int, j: int, v: A|
            0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s.update(j, v)[i] == s[i]
                && s.update(j, v)[j] == v,
        forall|s: Seq<A>, i: int, v: A|
            #![trigger s.update(i,v)[i]]
            0 <= i < s.len() ==> s.update(i, v)[i] == v,
{
}

#[verifier(external_body)] // new version of verus can proof this without external_body
pub proof fn map_insert_lemma<A, B>()
    ensures
        forall|m: Map<A, B>, x: A, y: A, v: B| x != y ==> m.insert(x, v)[y] == m[y],
{
}

#[verifier(external_body)]
pub proof fn seq_skip_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            s[0] != v && s.no_duplicates() ==> (s.skip(1).contains(v) == s.contains(v)),
        forall|s: Seq<A>| #![trigger s[0]] s.len() > 0 ==> s.contains(s[0]),
        forall|s: Seq<A>| #![trigger s[0]] s.len() > 0 ==> !s.skip(1).contains(s[0]),
        forall|s: Seq<A>, v: A| s[0] == v && s.no_duplicates() ==> s.skip(1) =~= s.remove_value(v),
        forall|s: Seq<A>, i: int| 0 <= i < s.len() - 1 ==> s.skip(1)[i] == s[i + 1],
{
}

#[verifier(external_body)]
pub proof fn seq_remove_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            s.contains(v) && s[i] != v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).contains(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            s.contains(v) && s[i] == v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).contains(v) == false,
        forall|s: Seq<A>, i: int, j: int|
            #![trigger s.subrange(0,i), s[j]]
            0 <= j < i ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int))[j] == s[j],
        forall|s: Seq<A>, i: int, j: int|
            #![trigger s.subrange(0,i), s[j+1]]
            i <= j < s.len() - 1 ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int))[j]
                == s[j + 1],
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.remove_value(v), s.subrange(0,i)]
            s.contains(v) && s[i] == v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ) == s.remove_value(v),
{
}

#[verifier(external_body)]
pub proof fn seq_remove_index_of_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            s.contains(v) && s[i] != v && s.no_duplicates() && s.subrange(0, i).contains(v) ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v),
        forall|s: Seq<A>, v: A, i: int|
        #![trigger s.index_of(v), s[i]]
            s.contains(v) && s[i] != v && s.no_duplicates() && s.index_of(v) < i ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            s.contains(v) && s[i] != v && s.no_duplicates() && s.subrange(i + 1, s.len() as int).contains(v) ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v) - 1,
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.index_of(v), s[i]]
            s.contains(v) && s[i] != v && s.no_duplicates() && s.index_of(v) > i ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).index_of(v) == s.index_of(v) - 1,
{}

pub proof fn seq_push_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() && s.contains(v) == false ==> s.push(v).no_duplicates() && s.push(
                v,
            ).index_of(v) == s.push(v).len() - 1,
        forall|s: Seq<A>, v: A, y: A|
            #![auto]
            s.no_duplicates() && s.contains(v) && s.contains(y) == false ==> s.push(y).index_of(v)
                == s.index_of(v),
{
    // Prove the first postcondition
    assert forall|s: Seq<A>, v: A| #![auto]
        s.no_duplicates() && s.contains(v) == false
    implies
        s.push(v).no_duplicates() && s.push(v).index_of(v) == s.push(v).len() - 1
    by {
        
        // Now prove that index_of(v) == s.push(v).len() - 1
        assert(s.push(v)[s.len() as int] == v);
        
    }

    // Prove the second postcondition
    assert forall|s: Seq<A>, v: A, y: A|
        s.no_duplicates() && s.contains(v) && s.contains(y) == false
    implies
        s.push(y).index_of(v) == s.index_of(v)
    by {
        // s.index_of(v) is some index i_v such that 0 <= i_v < s.len() && s[i_v] == v
        let i_v = s.index_of(v);
        
        // In s.push(y), the element at i_v is still s[i_v] because i_v < s.len()
        assert(s.push(y)[i_v] == v);
        
        // Since s has no duplicates and y is not in s, we know v != y
        assert(v != y);
        
        // Therefore, s.push(y).index_of(v) == i_v == s.index_of(v)
        assert(s.push(y).index_of(v) == i_v);
    }

}

pub proof fn seq_remove_lemma_2<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            x != v && s.no_duplicates() ==> s.remove_value(x).contains(v) == s.contains(v),
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() ==> s.remove_value(v).contains(v) == false,
{
    // Prove first postcondition
    assert forall|s: Seq<A>, v: A, x: A|
        x != v && s.no_duplicates() implies s.remove_value(x).contains(v) == s.contains(v)
    by {
        s.index_of_first_ensures(x);
        if s.contains(x) {
            let idx = s.index_of_first(x).unwrap();
            s.remove_ensures(idx);
            
            // Prove the forward direction: if s.remove_value(x).contains(v) then s.contains(v)
            if s.remove_value(x).contains(v) {
                let removed = s.remove_value(x);
                let i = removed.index_of(v);
                assert(removed[i] == v);
            }
            
            // Prove the backward direction: if s.contains(v) then s.remove_value(x).contains(v)
            if s.contains(v) {
                let j = s.index_of(v);
                let removed = s.remove_value(x);
                assert(removed.len() == s.len() - 1);
                
                if j < idx {
                    assert(removed[j] == v);
                    assert(removed.contains(v));
                } else {
                    // j > idx since j != idx
                    assert(removed[j - 1] == v);
                    assert(removed.contains(v));
                }
            }
        } else {
            // If s doesn't contain x, then remove_value(x) returns s unchanged
            assert(s.remove_value(x) == s);
        }
    };
    
    // Prove second postcondition
    assert forall|s: Seq<A>, v: A|
        #![auto]
        s.no_duplicates() implies s.remove_value(v).contains(v) == false
    by {
        s.index_of_first_ensures(v);
        if s.contains(v) {
            let idx = s.index_of_first(v).unwrap();
            s.remove_ensures(idx);
            
            let removed = s.remove_value(v);
            assert(removed.len() == s.len() - 1);
            
            // Prove by contradiction: assume removed contains v
            if removed.contains(v) {
                let i = removed.index_of(v);
                assert(0 <= i < removed.len());
                assert(removed[i] == v);
                assert(false);
            }
        } else {
            // If s doesn't contain v, then remove_value(v) returns s unchanged
            assert(s.remove_value(v) == s);
            assert(!s.contains(v));
        }
    };

}

#[verifier(external_body)]
pub proof fn seq_index_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int| #![trigger s[i]] s.no_duplicates() ==> s.index_of(s[i]) == i,
{
}

} // verus!
