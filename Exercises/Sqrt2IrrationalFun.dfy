// This file was automatically generated from Sqrt2IrrationalFun.dfy

// In this exercise, we will prove that the square root of 2 is irrational. Recall the definition of a rational number.
ghost predicate Rational(x: real) {
  exists n: int, m: int :: m > 0 && x == (n as real) / (m as real)
}

// We axiomatize the square root function
function Sqrt(x: real): real

// Non-negative.
lemma SqrtPos()
  ensures forall x: real :: Sqrt(x) >= 0.0

// The essence of square root.
lemma SqrtEssence()
  ensures forall x: real :: Sqrt(x) * Sqrt(x) == x

// Exercise
// The following lemma should prove very useful.
lemma SquareEven(x: int)
  requires (x * x) % 2 == 0
  ensures x % 2 == 0

// The absolute value function
function Abs(n: int): int {
  if n < 0 then -n else n
}

// Exercise
// Prove, constructively, that for any integer n and positive integer m, there exist another pair of integers with the same ratio such that they are not both even. Do it essentially like you would on paper, by crossing out occurences of 2 in a numerator and a denominator.
lemma NormalForm(n: int, m: int) returns (n': int, m': int)
  decreases Abs(n), Abs(m)
  requires m > 0
  ensures m' > 0
  ensures n' % 2 == 1 || m' % 2 == 1
  ensures (n as real) / (m as real) == (n' as real) / (m' as real)

// Exercise
// Prove that the square root of 2 is irrational. This can be done by contradiction. Assume that it were a rational number and consier its normal form, which we know exists. Since this normal form is such that at least either the numerator or the denominator is odd, a parity analysis should show that a number can be both even and odd at once, which of course is false.
lemma SqrtIrrational()
  ensures !Rational(Sqrt(2.0))

