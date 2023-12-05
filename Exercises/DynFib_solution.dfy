
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
{
  a := 0;
  var b: nat := 1;
  var i: nat := n;

  while i > 0
    invariant a == Fib(n - i)
    invariant b == Fib(n - i + 1)
  {
    a , b := b, a + b;
    i := i - 1;
  }
}

// Exercise
// Implement a dynamic programming version and verify that it agrees with the specification using a tail-rec spec.
method DynFib(n: nat) returns (a: nat)
  ensures a == Fib(n)
{

  a := 0;
  var b: nat := 1;
  var i: nat := n;

  while i != 0
    invariant Fib(n) == Fib'(i,a,b)
  {
    a , b := b, a + b;
    i := i - 1;
  }

}  

function Fib'(n: nat, n1: nat, n2: nat): nat
  ensures n > 0 ==> Fib'(n,n1,n2) == n1 * Fib(n-1) + n2 * Fib(n)
{ 
  match n {
    case 0 => n1
    case n => Fib'(n-1,n2,n1 + n2)
  }
}

