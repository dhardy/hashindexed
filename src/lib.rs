// Copyright 2016 hashindexed Developers
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Store a set of values in a data structure indexed by the hash of some
//! user-defined sub-property.
//! 
//! This works like a `HashSet<T>` with redefined equality and hash function on
//! T, but maintaining the usual definition of equality on T outside the
//! indexing.
//! 
//! See [`HashIndexed`](struct.HashIndexed.html) type for usage.

// Required for get(); will hopefully be stable soon
#![feature(set_recovery)]

use std::collections::HashSet;
use std::collections::hash_set;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::borrow::Borrow;
use std::fmt;

/// Configures how values are indexd.
/// 
/// User should either implement `extract_key()` or implement `key_eq()` and
/// `key_hash()` (in the latter case, `extract_key()` technically needs an
/// implementation but will never be used, so it can simply panic).
/// 
/// Note that `contains()`, `get()`, `replace()` and `remove()` require
/// implementation of `extract_key()` in order to function correctly!
pub trait KeyComparator<T, K> where K: Eq + Hash {
    /// This function should return a key extracted from the value.
    /// `eq` and `hash` are implemented on this key.
    /// 
    /// Note that the implementation could simply panic if `key_eq()` and
    /// `key_hash()` are implemented instead; however some functions
    /// will not work in this case.
    fn extract_key(value: &T) -> &K;
    
    /// Test equality of keys extracted from given values u, v.
    fn key_eq(u: &T, v: &T) -> bool {
        Self::extract_key(u) == Self::extract_key(v)
    }
    
    /// Generate a hash of a key retrieved from a given value.
    fn key_hash<H: Hasher>(value: &T, state: &mut H) {
        Self::extract_key(value).hash(state)
    }
}

/// Internal type
pub struct IndexableValue<T, K, E> {
    phantom_k: PhantomData<K>,
    phantom_e: PhantomData<E>,
    value: T
}
impl<T, K, E> IndexableValue<T, K, E> {
    fn new(value: T) -> IndexableValue<T, K, E> {
        IndexableValue {
            phantom_k: PhantomData,
            phantom_e: PhantomData,
            value: value
        }
    }
}

impl<T, K, E> PartialEq<IndexableValue<T, K, E>> for IndexableValue<T, K, E>
    where E: KeyComparator<T, K>, K: Eq + Hash
{
    fn eq(&self, other: &IndexableValue<T, K, E>) -> bool {
        E::key_eq(&self.value, &other.value)
    }
}
impl<T, K, E> Eq for IndexableValue<T, K, E> where E: KeyComparator<T, K>, K: Eq + Hash {}
impl<T, K, E> Hash for IndexableValue<T, K, E> where E: KeyComparator<T, K>, K: Eq + Hash {
    fn hash<H: Hasher>(&self, state: &mut H) {
        E::key_hash(&self.value, state)
    }
}
impl<T, K, E> Borrow<K> for IndexableValue<T, K, E>
    where E: KeyComparator<T, K>, K: Eq + Hash
{
    fn borrow(&self) -> &K {
        E::extract_key(&self.value)
    }
}


/// Stores a set of values indexed in a user-defined way.
/// 
/// Use like this:
/// 
/// ```
/// use hashindexed::{HashIndexed, KeyComparator};
/// 
/// #[derive(Debug, Eq, PartialEq)]
/// struct MyType { num: i32, name: &'static str }
/// 
/// struct MyComparator;
/// impl KeyComparator<MyType, i32> for MyComparator {
///     fn extract_key(v: &MyType) -> &i32 { &v.num }
/// }
/// 
/// let mut container: HashIndexed<MyType, i32, MyComparator> =
///     HashIndexed::new();
/// 
/// container.insert(MyType { num: 1, name: "one" });
/// container.insert(MyType { num: 2, name: "two" });
/// container.insert(MyType { num: 3, name: "three" });
/// 
/// assert_eq!( container.remove(&1).unwrap().name, "one" );
/// assert_eq!( container.remove(&1), None );
/// assert!( container.contains(&2) );
/// assert_eq!( container.len(), 2 );
/// 
/// assert_eq!( container.get(&3).unwrap().name, "three" );
/// container.replace(MyType { num: 3, name: "THREE" });
/// assert_eq!( container.get(&3).unwrap().name, "THREE" );
/// ```
pub struct HashIndexed<T, K, E> {
    set: HashSet<IndexableValue<T, K, E>>
}

impl<T, K, E> HashIndexed<T, K, E>
    where E: KeyComparator<T, K>, K: Eq + Hash,
    IndexableValue<T, K, E>: Borrow<K>
{
    /// Creates an empty HashIndexed collection.
    pub fn new() -> HashIndexed<T, K, E> {
        HashIndexed { set: HashSet::new() }
    }
    
    /// Creates an empty HashIndexed with space for at least `capacity`
    /// elements in the hash table.
    pub fn with_capacity(capacity: usize) -> HashIndexed<T, K, E> {
        HashIndexed { set: HashSet::with_capacity(capacity) }
    }
    
    /// Returns the number of elements the collection can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.set.capacity()
    }
    
    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the collection. More spaces than this may be allocated to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.set.reserve(additional)
    }
    
    /// Shrinks the capacity of the collection as much as possible. It will
    /// drop down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.set.shrink_to_fit()
    }
    
    /// An iterator visiting all elements in arbitrary order.
    pub fn iter(&self) -> Iter<T, K, E> {
        Iter { iter: self.set.iter() }
    }

    /// Creates a consuming iterator, that is, one that moves each value out
    /// of the set in arbitrary order. The set cannot be used after calling
    /// this.
    pub fn into_iter(self) -> IntoIter<T, K, E> {
        IntoIter { iter: self.set.into_iter() }
    }
    
    /// Returns the number of elements in the collection.
    pub fn len(&self) -> usize { self.set.len() }

    /// Returns true if the collection contains no elements.
    pub fn is_empty(&self) -> bool { self.set.is_empty() }
    
    /// Clears the collection, removing all values.
    pub fn clear(&mut self) { self.set.clear() }
    
    /// Returns `true` if the collection contains a value matching the given
    /// key.
    pub fn contains(&self, k: &K) -> bool {
        self.set.contains(k)
    }
    /// Returns a reference to the value corresponding to the key.
    pub fn get(&self, k: &K) -> Option<&T> {
        self.set.get(k).map(|v| &v.value)
    }
    
    /// Adds a value to the set. Returns true if the value was not already
    /// present in the collection.
    pub fn insert(&mut self, value: T) -> bool {
        self.set.insert(IndexableValue::new(value))
    }
    
    /// Adds a value to the set, replacing the existing value, if any, that is
    /// equal to the given one. Returns the replaced value.
    pub fn replace(&mut self, value: T) -> Option<T> {
        //TODO: what's this `Recover::replace(&mut self.set, value)` thing?
        let removed = self.remove(E::extract_key(&value));
        self.insert(value);
        removed
    }
    
    /// Removes and returns the value in the collection, if any, that is equal
    /// to the given one.
    pub fn remove(&mut self, k: &K) -> Option<T> {
        // Note that 'take' in HashSet corresponds to 'remove' for values in
        // HashMap; this is because it was added after API stabilisation of the
        // existing 'remove' function.
        self.set.take(k).map(|v| v.value)
    }
}

impl<T, K, E> PartialEq for HashIndexed<T, K, E>
    where HashSet<IndexableValue<T, K, E>>: PartialEq
{
    fn eq(&self, other: &HashIndexed<T, K, E>) -> bool {
        self.set == other.set
    }
}

impl<T, K, E> Eq for HashIndexed<T, K, E>
    where HashIndexed<T, K, E>: PartialEq
{}

impl<T, K, E> fmt::Debug for HashIndexed<T, K, E>
    where HashSet<IndexableValue<T, K, E>>: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.set.fmt(f)
    }
}

/// HashIndexed iterator
pub struct Iter<'a, T: 'a, K: 'a, E: 'a> {
    iter: hash_set::Iter<'a, IndexableValue<T, K, E>>
}

/// HashIndexed move iterator
pub struct IntoIter<T, K, E> {
    iter: hash_set::IntoIter<IndexableValue<T, K, E>>
}

impl<'a, T, K, E> IntoIterator for &'a HashIndexed<T, K, E>
    where K: Eq + Hash, E: KeyComparator<T, K>,
    IndexableValue<T, K, E>: Borrow<K>
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, K, E>;
    fn into_iter(self) -> Iter<'a, T, K, E> {
        self.iter()
    }
}

impl<'a, T, K, E> IntoIterator for HashIndexed<T, K, E>
    where K: Eq + Hash, E: KeyComparator<T, K>
{
    type Item = T;
    type IntoIter = IntoIter<T, K, E>;
    fn into_iter(self) -> IntoIter<T, K, E> {
        self.into_iter()
    }
}

impl<'a, T, K, E> Iterator for Iter<'a, T, K, E> {
    type Item = &'a T;
    
    fn next(&mut self) -> Option<&'a T> { self.iter.next().map(|x| &x.value) }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
impl<'a, T, K, E> ExactSizeIterator for Iter<'a, T, K, E> {
    fn len(&self) -> usize { self.iter.len() }
}

impl<T, K, E> Iterator for IntoIter<T, K, E> {
    type Item = T;

    fn next(&mut self) -> Option<T> { self.iter.next().map(|x| x.value) }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
impl<T, K, E> ExactSizeIterator for IntoIter<T, K, E> {
    fn len(&self) -> usize { self.iter.len() }
}
