

// In this exercise, we will formalize arithmetic on natural numbers. We start by declaring the type of natural numbers, which we declare to be non-empty.
type Nat(00)

// There is a single constant symbol that represents 0.
ghost const Zero: Nat

// The successor function is named S. If n is a natural number, S returns n + 1. If S(x) is a natural number, we call x its predecessor.
ghost function S(x: Nat): Nat

// Addition.
ghost function Plus(x: Nat, y: Nat): Nat

// Multiplication.
ghost function Times(x: Nat, y: Nat): Nat

// A predicate to test whether two natural numbers are equal.
ghost predicate Eq(x: Nat, y: Nat)

// Exercise
// Define Eq as being reflexive.
lemma IdentityPrinciple()

// Exercise
// Define the Leibniz equality axiom: if two numbers are equal, they satisfy the same properties.
lemma Leibniz()

// Exercise
// If two successors are equal, then so are their predecessors.
lemma Peano1()

// Exercise
// Zero is not the successor of any natural number
lemma Peano2()

// Exercise
// Induction principle. Assume that some property holds for Zero, and that if it holds for n, then it also holds for its successor. Then, the property holds for any natural number.
lemma Peano3()
  
// Exercise
// Definition of addition. Zero is a neutral element for addition.
lemma Peano4()

// Exercise
// Definition of addition. Additional and successor are interchangeable.
lemma Peano5()

// Exercise
// Definition of multiplication. Zero is a cancelling element for multiplication
lemma Peano6()

// Exercise
// Definition of multiplication. Multiplication of a number n by a successor is adding n to the multiplication of the predecessor.
lemma Peano7()

// Exercise
// Equality is transitive.
lemma EqTransitive()
