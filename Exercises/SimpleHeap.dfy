// This file was automatically generated from SimpleHeap.dfy

// Exercise
// Implement the following method to satisfy this specification.
method Mystery(a: array<int>, i: nat, j: nat)
  modifies a
  requires i < a.Length && j < a.Length
  ensures old(a[i]) == a[j] && old(a[j]) == a[i]

// Consider the following definition of a reference.
type ref<T> = a: array<T> | a.Length == 1 witness *

// And the definition of an even natural number
ghost predicate Even(a: nat) {
  exists b: nat :: a == 2 * b
}

// Exercise
//  Implement and verify the following method to satisfy its postcondition.
method Arbitrary(s: ref<nat>)
  modifies s
  ensures s[0] == 4 * old(s[0]) * old(s[0])
  ensures Even(s[0])

// Exercise
// Implement and verify a method that goes over an array and for all index i, sets a[i] to a[i].
method DoNothing(a: array<int>)
  modifies a
  ensures forall i: nat :: i < a.Length ==> old(a[i]) == a[i]

