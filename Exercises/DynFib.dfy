// This file was automatically generated from DynFib.dfy

// Following is a specification of the Fibonacci function.
function Fib(n: nat): nat {
  match n {
    case 0 => 0
    case 1 => 1
    case n => Fib(n-1) + Fib(n-2)
  }
}

// Exercise
// Implement a dynamic programming version and verify that it agrees with the specification directly.
method DynFib2(n: nat) returns (a: nat)
  ensures a == Fib(n)

// Exercise
// Implement a dynamic programming version and verify that it agrees with the specification using a tail-rec spec.
method DynFib(n: nat) returns (a: nat)
  ensures a == Fib(n)

