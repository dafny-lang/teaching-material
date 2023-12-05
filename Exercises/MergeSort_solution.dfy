// Exercise
// In this exercise, we will define and partially verify mergesort using dependent verification. First, define an ordered sequence.
predicate ordered(s: seq<int>) 
{
  forall i: nat :: 0 < i < |s| ==> s[i-1] <= s[i]
}

// Exercise
// Define the merge function.
function merge(s1: seq<int>, s2: seq<int>): seq<int>
  requires ordered(s1)
  requires ordered(s2)
  ensures ordered(merge(s1,s2))
{
  if |s1| == 0 then s2 else if |s2| == 0 then s1 else
    if s1[0] <= s2[0] then [s1[0]] + merge(s1[1..],s2) else [s2[0]] + merge(s1,s2[1..]) 
}

// Exercise
// Define the mergesort function.
function mergesort(s: seq<int>): seq<int>
  ensures ordered(mergesort(s))
{
  if |s| < 2 then s else
    merge(mergesort(s[..|s|/2]),mergesort(s[|s|/2..]))
}

