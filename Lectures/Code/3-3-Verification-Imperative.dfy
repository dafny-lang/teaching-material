module FormalizingMathematics_Pre {

  type T

}

module Imperative_Pre {

  ghost predicate Even(a: nat) {
    exists b: nat :: a == 2 * b
  }

  ghost predicate Odd(a: nat) {
    !Even(a)
  }

}

module Imperative_PreHT' {

  type T

  predicate P(x: T)
  predicate Q(x: T)
  predicate R()
  predicate S()

}

module FunctionalProgramming_Pre {

  type Type(0)
  type X(0)
  type Y(0)
  type R = Type
  const expression: R
  datatype TypeConstructor<T> = Nil
  const booleanExpression: bool

}

module ImperativeProgramming_M2Pre {

  const integerExpression: int

}

module CombiningProofAndFP_Pre {

  datatype List<T> =
    | Nil
    | Cons(head: T, tail: List)

  function Length<T>(l: List): nat {
    match l
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
  }

}

module Imperative_PreHT {

  predicate P()
  predicate Q()
  predicate R()
  predicate S()

}

module ImperativeProgramming_PreMatch {

  datatype DT =
    | Case1
    | Case2

  const datatypeValue: DT

}

module ProofMethod_Base {

  ghost const cond: bool

  ghost const A: bool
  ghost const B: bool
  ghost const C: bool

  ghost predicate P<T>(x: T)
  ghost predicate Q<T>(x: T)
  ghost predicate R<T>(x: T)
  ghost predicate S<T>(x: T)

}

module ProvingByConvincing_PreReq {

  predicate P()
  predicate Q()
  predicate R()
  ghost const A: bool 
  ghost const B: bool

}

module ProvingByConvincing_PreReq2 {

  predicate P(x: nat)
  predicate Q(x: nat)
  ghost const c: nat

}

module Mathematics_Pre {

  ghost predicate Even(n: nat) {
    exists m: nat :: n == 2 * m
  }

  ghost predicate Odd(n: nat) {
    !Even(n)
  }

}

module ImperativeProgramming_PreFlow {

  const booleanExpression: bool
  const booleanExpressionA: bool
  const booleanExpressionB: bool

  type Smaller = x: int | x <= 0
  type Larger = x: int | 0 <= x
  const loExpression: Smaller
  const hiExpression: Larger


}

// Slide 1 Methods

module Imperative_A1 {
  
    method Example(x: nat, y: nat) returns (z: nat) {
      var t: nat := 0;
      z := 0;
      for i := 0 to x {
        z := z + y;
      }
      z := t;
    }
  
  }
  // Slide 2 Verifying methods

module Imperative_A1' {
  
    method Example(x: int, y: int) returns (z: int)
      requires x > 0
      requires y > 0
      ensures z == x + y
      ensures z > 0
    {
      z := x + y;
    }
  
  }
  // Slide 3 Methods and termination

module Imperative_A2 {
  
    method Bad(x: nat)
      ensures false
      decreases *
    {
      Bad(x + 1);
    }
  
  }
  // Slide 4 Methods and termination -- danger

module Imperative_A3 {
  
    import opened Imperative_A2
  
    method CorrectIsh()
      ensures 0 == 1
      decreases *
    {
      Bad(0);
    }
  
  }
  // Slide 5 When verification fails

// Slide 6 Floyd logic -- 1

module Imperative_A4 {
  
    method MixedCodeAndProof(x: nat) returns (y: nat)
      requires x > 1
      ensures y > x
    {
      y := x + 2;
      assert y == x + 2;
      y := 2 * y;
      assert y == 2 * x + 4;
      y := y - 5;
      assert y == 2 * x - 1;
    }
  
  }
  // Slide 7 Floyd logic -- 2

module Imperative_A5 {
  /*    This example also shows italicized text on the slide
  
    method MixedCodeAndProof(x: nat) returns (y: nat, ghost g: int)
      \(_`requires` x > 1_\)
      \(_`ensures` y > x_\)
    {
      y := x + 2;
      y := 2 * y;
      \(_g := y + 10;_\)
      y := y - 5;
      \(_`assert` y > x `by` {_\)
        \(_`assert` y == 2 * x - 1;_\)
        \(_`assert` 2 * x - x > 1;_\)
      \(_}_\)
    }
  
  */  
  }
  // Slide 8 Hoare triples

// Slide 9 Call

module Imperative_HT0 {

  import opened Imperative_PreHT

  method M()
    requires Q()
    ensures R()

  method Call()
    requires P()
    requires P() ==> Q()
    requires R() ==> S()
    ensures S()
  {
    M();
  }


}
// Slide 10 Sequencing

module Imperative_HT1 {

  import opened Imperative_PreHT

  method S1()
    requires P()
    ensures Q()

  method S2()
    requires Q()
    ensures R()

  method Sequencing()
    requires P()
    ensures R()
  {
    S1();
    S2();
  }


}
// Slide 11 Variable update

module Imperative_HT2 {

  import opened Imperative_PreHT'

  method M() returns (o: T)
    ensures forall t: T :: P(t)

  method Update() returns (o: T)
    ensures P(o)
  {
    o := M();
  }


}
// Slide 12 Loops

module Imperative_A6 {
  
    method Times(x: nat, y: nat) returns (z: nat)
      ensures x * y == z
    {
      z := 0;
      for i := 0 to x
        invariant i * y == z
      {
        z := z + y;
      }
    }
  
  }
  // Slide 13 Case study -- 1

module FailImperative_A7 {
  
    import opened Imperative_Pre
  
    method {:verify false}M(a: nat) returns (b: nat)
      ensures Even(b)
    {
      b := 2 * a;
      b := b * b;
    }
  
  }
  // Slide 14 Case study -- 2

module Imperative_A8 {
  
    import opened Imperative_Pre
  
    method M(a: nat) returns (b: nat)
      ensures Even(b)
    {
      b := 2 * a;
      assert Even(b);
      b := b * b;
      assert Even(b) by {
        assert exists c: nat :: b == 2 * c by {
          assert b == (2 * a) * (2 * a);
          assert b == 2 * (2 * a * a);
        }
      }
    }
  
  }
  // Slide 15 Case study -- 3

module Imperative_A9 {
  
    import opened Imperative_Pre
  
    method M(a: nat) returns (b: nat)
      ensures Even(b)
    {
      var b0: nat := 2 * a;
      assert Even(b0);
      b := b0 * b0;
      assert Even(b) by {
        assert exists c: nat :: b == 2 * c by {
          var c: nat :| b0 == 2 * c;
          assert b == (2 * c) * (2 * c);
          assert b == 2 * (2 * c * c);
        }
      }
    }
  
  }
  // Slide 16 Weaving proof and code

// Slide 17 Case study -- 4

module Imperative_A10 {
  
    import opened Imperative_Pre
  
    method M(a: nat) returns (b: nat)
      ensures Even(b)
    {
      b := 2 * a;
      ghost var b0: nat := b;
      assert Even(b0);
      b := b * b;
      assert Even(b) by {
        assert exists c: nat :: b == 2 * c by {
          var c: nat :| b0 == 2 * c;
          assert b == (2 * c) * (2 * c);
          assert b == 2 * (2 * c * c);
        }
      }
    }
  
  }
  // Slide 18 Case study -- 5

module Imperative_A11 {

  import opened Imperative_Pre

  method M(a: nat, p: nat) returns (b: nat)
    ensures Even(b)
  {
    b := 2 * a;
    assert Even(b);
    for i := 0 to p
      invariant Even(b)
    {
      ghost var b0: nat := b;
      b := b * b;
      assert Even(b) by {
        assert exists c: nat :: b == 2 * c by {
          var c: nat :| b0 == 2 * c;
          assert b == (2 * c) * (2 * c);
          assert b == 2 * (2 * c * c);
        }
      }
    }
  }

}
// Slide 19 Functional code as specification -- 1

// Slide 20 Functional code as specification -- 2

module FailImperative_A12 {
  
    import opened Imperative_A13
  
    method {:verify false}Times(x: nat, y: nat) returns (z: nat)
      ensures z == Timesf(x, y)
    {
      z := 0;
      for i := 0 to x {
        z := z + y;
      }
    }
  
  }
  // Slide 21 Functional code as specification -- 3

module Imperative_A13 {
  
    function Timesf(x: nat, y: nat): nat {
      if x == 0 then 0 else y + Timesf(x - 1, y)
    }
  
  }
  // Slide 22 Functional code as specification -- 4

module Imperative_A14 {
  
    import opened Imperative_A13
  
    method Times(x: nat, y: nat) returns (z: nat)
      ensures z == Timesf(x, y)
    {
      z := 0;
      for i := 0 to x
        invariant z == Timesf(i, y)
      {
        z := z + y;
      }
    }
  
  }
  // Slide 23 Functional code as specification -- 5

module Imperative_A15 {
  
    import opened Imperative_A13
  
    lemma TimesfCommutative(x: nat, y: nat)
      ensures Timesf(x, y) == Timesf(y, x)
    {
      if x == 0 {
      } else {
        TimesfCommutative(x - 1, y);
      }
    }
  
  }
  // Slide 24 Functional code as specification -- 6

// Slide 25 Function by method

module Imperative_A16 {
  
    function Timesf(x: nat, y: nat): nat
    {
      if x == 0 then 0 else y + Timesf(x - 1, y)
    } by method {
      var z := 0;
      for i := 0 to x
        invariant z == Timesf(i, y)
      {
        z := z + y;
      }
      return z;
    }
  
  }
  // Slide 26 Arrays -- introduction

module Imperative_BA10 {
  
    import opened Imperative_BPre
  
    method M(a: array<int>)
      requires a.Length > 10
      modifies a
    {
      var x: int := a[3];
      a[5] := 6;
      var b: array<int> := new int[5];
    }
  
  }
  // Slide 27 Programming with references

module Imperative_BPre {
  
    type Ref<T> = a: array<T> | a.Length == 1 witness *
  
  }
  // Slide 28 Reasoning with references

// Slide 29 Reading from the state

module Imperative_BA1 {
  
    import opened Imperative_BPre
  
    function Read(s: seq<Ref<nat>>, idx: nat): nat
      requires idx < |s|
      reads s[idx]
    {
      s[idx][0]
    }
  
  }
  // Slide 30 Summary of function types

// Slide 31 Reading the state

module Imperative_BA2 {
  
    import opened Imperative_BPre
  
    method M(s: Ref<nat>)
    {
      print s[0];
    }
  
  }
  // Slide 32 Modifying the state

module Imperative_BA3 {
  
    import opened Imperative_BPre
  
    method Write(s: seq<Ref<nat>>, idx: nat, v: nat)
      requires idx < |s|
      modifies s[idx]
    {
      s[idx][0] := v;
    }
  
  }
  // Slide 33 Referring to old state

module Imperative_BA4 {

  import opened Imperative_BPre

  method Add(c: Ref<nat>)
    modifies c
    ensures c[0] % 2 == 0 <==> old(c[0]) % 2 == 0
  {
    c[0] := c[0] + 2;
  }

}
// Slide 34 Aliasing -- 1

module FailImperative_BA5 {
  
    import opened Imperative_BPre
  
    method {:verify false} InitIncorrect(c1: Ref<nat>, c2: Ref<nat>)
      modifies c2
      ensures old(c1[0]) == c1[0]
    {
      c2[0] := 2;
    }
  
  }
  // Slide 35 Aliasing -- 2

module Imperative_BA6 {

  import opened Imperative_BPre

  method Init(c1: Ref<nat>, c2: Ref<nat>)
    requires c1 != c2
    modifies c2
    ensures old(c1[0]) == c1[0]
  {
    c2[0] := 2;
  }

}
// Slide 36 Frames -- 1

// Slide 37 Frames -- 2

module FailImperative_BA7 {
  
    import opened Imperative_BPre
    import opened Imperative_BA1
    import opened Imperative_BA3
  
    method {:verify false} TestIncorrect(s: seq<Ref<nat>>) returns (x: nat, y: nat)
      requires |s| > 10
      modifies s
      ensures x == y
    {
      x := Read(s, 5);  // read from the object referenced by s[5]
      Write(s, 2, 56);  // write to the object referenced by s[2]
      y := Read(s, 5);  // read from the object referenced by s[5] again
    }
  
  }
  // Slide 38 Aliasing -- 3

module Imperative_BA8 {
  
    import opened Imperative_BPre
    import opened Imperative_BA1
    import opened Imperative_BA3
  
    method Test(s: seq<Ref<nat>>) returns (x: nat, y: nat)
      requires |s| > 10
      requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
      modifies s
      ensures x == y
    {
      x := Read(s, 5);
      Write(s, 2, 56);
      y := Read(s, 5);
    }
  
  }
  // Slide 39 Labels

module Imperative_BA9 {
  
    import opened Imperative_BPre
  
    method M(c: Ref<nat>)
      modifies c
      ensures c[0] % 2 == 1
    {
      c[0] := 2 * c[0];
      label L:
      c[0] := c[0] + 1;
      assert old@L(c[0]) % 2 == 0;
      assert c[0] % 2 == 1;
    }
  
  }
  // Slide 40 Arrays -- ranges

module Imperative_BA11 {

  import opened Imperative_BPre

  lemma ArrayUnchanged<T>(a: array)
    ensures a[..] == old(a[..])

}
// Slide 41 Fresh

module Imperative_BA13 {
  
    import opened Imperative_BPre
    import opened Imperative_BA12
  
    method Needfresh(a: array<int>)
      requires a.Length > 10
    {
      var b: array<int> := Copy(a);
      b[5] := 8;
    }
  
  }
  // Slide 42 Arrays -- example

module Imperative_BA12 {

  import opened Imperative_BPre

  method Copy(a: array<int>) returns (b: array<int>)
    ensures a.Length == b.Length
    ensures forall i: nat :: i < a.Length ==> a[i] == b[i]
    ensures fresh(b)
  {
    b := new int[a.Length];
    for i := 0 to a.Length
      invariant i <= a.Length
      invariant forall j: nat :: j < i ==> a[j] == b[j]
    {
      b[i] := a[i];
    }
  }

}
// Slide 43 Unchanged

module Imperative_BA13_1 {

  class O {
    var x: int
    var y: int
  }

  method Unchanged(o: O)
    ensures unchanged(o) <==> o.x == old(o.x) && o.y == old(o.y)
  {
  }

}
// Slide 44 Allocated

module Imperative_BA13_2 {

  class O {}

  method Allocated(o: O)
    ensures !old(allocated(o)) <==> fresh(o)
  {
  }

}
// Slide 45 Two-state predicates

module Imperative_BA14 {
  
    import opened Imperative_BPre
  
    twostate predicate NoChange<T>(a: array)
      reads a
    {
      a[..] == old(a[..])
    }
  
  }
  