mod sorted_vec;
mod selection_vec;
pub use selection_vec::SelectionVecDatabase;
mod unsorted_vec;
pub use unsorted_vec::UnsortedVecDatabase;
mod binary_search_vec;
pub use binary_search_vec::BinarySearchVecDatabase;
#[cfg(test)]
mod tests;
pub use sorted_vec::SortedVecDatabase;

use vstd::prelude::*;

pub type KeyType = i32;
pub type ValueType = i32;

verus! {

// abstract view of any implementation of the database is an abstract map
pub trait Database: View<V = Map<KeyType, ValueType>> {
    fn get(&self, key: &KeyType) -> (result: Option<&ValueType>)
        ensures
            match result {
                Some(value) => self@.dom().contains(*key) && self@[*key] == *value,
                None => !self@.dom().contains(*key),
            };

    fn scan(&self, lo: &KeyType, hi: &KeyType) -> (list: Vec<(KeyType, ValueType)>)
        requires *lo <= *hi,
        ensures
            // each K/V pair in list is unique
            forall|i: int, j: int| #![trigger list@[i], list@[j]] 0 <= i < j < list@.len() ==> list@[i] != list@[j],
            // all returned K/V pairs are within range
            forall|i: int| #![trigger list@[i]] 0 <= i < list@.len() ==> *lo <= list@[i].0 <= *hi,
            // all pairs in range should appear in the final result
            forall|k: KeyType| #![trigger self@.dom().contains(k)] self@.dom().contains(k) && *lo <= k <= *hi ==> list@.contains((k, self@[k])),
            // all pairs in the final result are real
            forall|i: int| #![trigger list@[i]] 0 <= i < list@.len() ==> self@.dom().contains(list@[i].0) && self@[list@[i].0] == list@[i].1
        ;
    
    fn sort(&self) -> (list: Vec<(KeyType, ValueType)>)
        ensures
            // all pairs in list appear in db
            forall|i: int| #![trigger list@[i]] 0 <= i < list@.len() ==> self@.dom().contains(list@[i].0) && self@[list@[i].0] == list@[i].1,
            // ... and all pairs in the db appear in the result list
            forall|k: KeyType| #![trigger self@.dom().contains(k)] self@.dom().contains(k) ==> list@.contains((k, self@[k])),
            // all pairs in the result list are sorted by key (no duplicated keys)
            forall|i: int, j: int| #![trigger list@[i], list@[j]] 0 <= i < j < list@.len() ==> list@[i].0 < list@[j].0,
        ;
            
}
}
