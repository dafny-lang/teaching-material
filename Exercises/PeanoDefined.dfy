// This file was automatically generated from PeanoDefined.dfy

// We formalize Peano arithmetic again, but this time, we will define the type of natural numbers instead of declaring it. Also, we will prove the propositions that were previously axioms.
datatype Nat =
  | Zero
  | S(x: Nat)

// Exercise
// Define addition
function Plus(x: Nat, y: Nat): Nat

// Exercise
// Define multiplication
function Times(x: Nat, y: Nat): Nat

// Exercise
// Define equality
predicate eq(x: Nat, y: Nat)

// Exercise
// Prove
lemma IdentityPrinciple()
  ensures forall x: Nat :: eq(x,x)

// Exercise
// Prove
lemma Leibniz()
  ensures forall P: Nat -> bool :: forall x, y: Nat :: eq(x,y) ==> P(x) ==> P(y)

// Exercise
// Prove
lemma Peano1()
  ensures forall x, y: Nat :: eq(S(x),S(y)) ==> eq(x,y)

// Exercise
// Prove
lemma Peano2()
  ensures forall x: Nat :: !(eq(Zero,S(x)))

// Exercise
// Prove
lemma Peano3Pre(P: Nat -> bool, y: Nat)
  requires P(Zero)
  requires forall x: Nat :: P(x) ==> P(S(x))
  ensures P(y)

// Exercise
// Prove
lemma Peano3()
  ensures forall P: Nat -> bool :: ((P(Zero)) && (forall x: Nat :: P(x) ==> P(S(x)))) ==> forall y: Nat :: P(y)

// Exercise
// Prove
lemma Peano4()
  ensures forall x: Nat :: eq(Plus(Zero,x),x)

// Exercise
// Prove
lemma Peano5()
  ensures forall x, y: Nat :: eq(Plus(S(x),y),S(Plus(x,y)))

// Exercise
// Prove
lemma Peano6()
  ensures forall x: Nat :: eq(Times(Zero,x),Zero)

// Exercise
// Prove
lemma Peano7()
  ensures forall x, y: Nat :: eq(Times(S(x),y),Plus(Times(x,y),y))

