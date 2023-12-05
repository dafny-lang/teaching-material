// FSum takes a sequence of natural numbers as an input and compute their sum. The goal of this exercise is to reimplement it imperatively and prove that it matches this functional specification.
function FSum(s: seq<nat>): nat {
  if |s| == 0 then 0 else s[0] + FSum(s[1..])
}

// Exercise
// To make things easier, you can start by implementing a tail-recursive version of FSum and prove their relation.
function FSum'(s: seq<nat>, acc: nat): nat
  ensures FSum'(s,acc) == acc + FSum(s)
{
  if |s| == 0 then acc else FSum'(s[1..],acc + s[0])
}

// Exercise
// Implement a method that behaves like FSum.
method sum(s: seq<nat>) returns (r: nat)
  ensures r == FSum(s)
{
  if |s| == 0 {
    return 0;
  }
  r := 0;
  var i: nat := 0;
  while i < |s|
    invariant i <= |s|
    invariant FSum(s) == FSum'(s[i..],r)
  {
    r := r + s[i];
    i := i + 1;
  }
}

// Exercise
// If you did use FSum' in the invariant of the previous method, do it again without calling FSum'.
method sum2(s: seq<nat>) returns (r: nat)
  ensures r == FSum(s)
{
  if |s| == 0 {
    return 0;
  }
  r := 0;
  var i: nat := 0;
  while i < |s|
    invariant i <= |s|
    invariant FSum(s) == r + FSum(s[i..])
  {
    r := r + s[i];
    i := i + 1;
  }
}

