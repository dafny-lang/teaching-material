// This file was automatically generated from Summation.dfy
// FSum takes a sequence of natural numbers as an input and compute their sum. The goal of this exercise is to reimplement it imperatively and prove that it matches this functional specification.
function FSum(s: seq<nat>): nat {
  if |s| == 0 then 0 else s[0] + FSum(s[1..])
}

// Exercise
// To make things easier, you can start by implementing a tail-recursive version of FSum and prove their relation.
function FSum'(s: seq<nat>, acc: nat): nat
  ensures FSum'(s,acc) == acc + FSum(s)

// Exercise
// Implement a method that behaves like FSum.
method sum(s: seq<nat>) returns (r: nat)
  ensures r == FSum(s)

// Exercise
// If you did use FSum' in the invariant of the previous method, do it again without calling FSum'.
method sum2(s: seq<nat>) returns (r: nat)
  ensures r == FSum(s)

