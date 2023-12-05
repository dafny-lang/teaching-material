// This file was automatically generated from PrefixSum.dfy
// FSum takes a sequence of natural numbers as an input and compute their sum. 
function FSum(s: seq<nat>): nat {
  if |s| == 0 then 0 else s[0] + FSum(s[1..])
}

// Exercise
// Implement and verify the prefix sum algorithm, whose specification is given as a postcondition.
method PSum(a: array<nat>)
  modifies a
  requires a.Length > 1
  ensures forall i: nat :: i < a.Length ==> a[i] == FSum(old(a[..(i+1)]))


