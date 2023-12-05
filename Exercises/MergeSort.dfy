// This file was automatically generated from MergeSort.dfy
// Exercise
// In this exercise, we will define and partially verify mergesort using dependent verification. First, define an ordered sequence.
predicate ordered(s: seq<int>) 

// Exercise
// Define the merge function.
function merge(s1: seq<int>, s2: seq<int>): seq<int>
  requires ordered(s1)
  requires ordered(s2)
  ensures ordered(merge(s1,s2))

// Exercise
// Define the mergesort function.
function mergesort(s: seq<int>): seq<int>
  ensures ordered(mergesort(s))

