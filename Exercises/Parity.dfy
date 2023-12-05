// This file was automatically generated from Parity.dfy
// A natural is *even* if it is a multiple of 2.
ghost predicate even(a: nat) {
  exists b: nat :: a == 2 * b
}

// A natural is *odd* if it is not even.
ghost predicate odd(a: nat) {
  !even(a)
}

// Exercise
// Prove that the square of an even natural is even.
lemma even_prop_1()
  ensures forall n: nat :: even(n) ==> even(n * n)

// Exercise
// Prove that the sum of two even naturals is even.
lemma even_prop_2()
  ensures forall n: nat, m: nat :: even(n) && even(m) ==> even(n + m)

// Exercise
// Prove that a number is odd if and only if it is 1 plus a multiple of 2.
lemma odd_representation(a: nat)
  ensures odd(a) <==> exists b: nat :: a == 2 * b + 1

// Exercise
// Prove that if a square natural is even, so is its square root.
lemma square_even(n: nat)
  requires even(n * n)
  ensures even(n)
