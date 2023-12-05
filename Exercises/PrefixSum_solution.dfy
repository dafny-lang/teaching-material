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
{
  for i := 1 to a.Length
    invariant i <= a.Length
    invariant forall j: nat :: j < i ==> a[j] == FSum(old(a[..(j+1)]))
    invariant forall j: nat :: i <= j < a.Length ==> old(a[j]) == a[j]
  {
    assert forall j: nat :: j < i ==> a[j] == FSum(old(a[..(j+1)]));
    a[i] := a[i] + a[i-1];
    assert forall j: nat :: j < i ==> a[j] == FSum(old(a[..(j+1)]));
    assert a[i] == old(a[i]) + a[i-1];
    assert a[i-1] == FSum(old(a[..i]));
    FSum_inv(old(a[..i]),old([a[i]]));
    assert old(a[..(i+1)]) == old(a[..i]) + old([a[i]]);
  }
} 

function FSum'(s: seq<nat>, acc: nat): nat
  ensures FSum'(s,acc) == acc + FSum(s) 
{ 
  if |s| == 0 then acc else FSum'(s[1..],acc + s[0])
} 

lemma FSum'_inv(s1: seq<nat>, s2: seq<nat>, acc: nat)
  ensures FSum'(s1 + s2,acc) == FSum'(s2,FSum'(s1,acc))
{ 
  if |s1| == 0 {
    assert FSum'(s1,acc) == acc;
    assert s1 + s2 == s2;
  } else {
    FSum'_inv(s1[1..],s2,acc + s1[0]);
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
  }
} 

lemma FSum_inv(s1: seq<nat>, s2: seq<nat>)
  ensures FSum(s1 + s2) == FSum(s1) + FSum(s2)
{ 
  assert FSum(s1) + FSum(s2) == FSum'(s2,FSum(s1));
  assert FSum'(s2,FSum(s1)) == FSum'(s2,FSum'(s1,0));
  assert FSum'(s2,FSum'(s1,0)) == FSum'(s1 + s2, 0) by {
    FSum'_inv(s1,s2,0);
  }
}


