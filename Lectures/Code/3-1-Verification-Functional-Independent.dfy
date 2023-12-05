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

// Slide 1 Verification of functional programs

// Slide 2 Verification of functional code -- specification

module FPVerification_A10 {
  
    function Increment(n: int): int {
      n + 1
    }
  
    lemma IncrementLarger()
      ensures forall n: int :: Increment(n) > n
  
    lemma InrementEvenIsOdd()
      ensures forall n: int :: n % 2 == 0 ==> Increment(n) % 2 == 1
  
  }
  // Slide 3 Verifying functional code -- proof

// Slide 4 Conditional

module FPVerification_A10_1 {

  function Abs(x: int): int {
    if x < 0 then -x else x
  }

  lemma AbsPositive(x: int)
    ensures Abs(x) >= 0
  {
    if x < 0 {
      assert -x > 0;
    } else {
      assert x >= 0;
    }
  }

}
// Slide 5 Pattern matching

module FPVerification_A10_2 {

  datatype Size =
    | Small
    | Large

  function Ounces(s: Size): int {
    match s
    case Small => 4
    case Large => 8
  }

  lemma OuncesMultiple4(s: Size)
    ensures exists n: int :: Ounces(s) == 4 * n
  {
    match s
    case Small =>
      assert Ounces(s) == 4 * 1;
    case Large =>
      assert Ounces(s) == 4 * 2;
  }

}
// Slide 6 Example 1

module FPVerification_A11 {

  function Increment(n: int): int {
    n + 1
  }

  lemma IncrementLarger()
    ensures forall n: int :: Increment(n) > n
  {}

  lemma InrementEvenIsOdd()
    ensures forall n: int :: n % 2 == 0 ==> Increment(n) % 2 == 1
  {
    forall n: int
      ensures n % 2 == 0 ==> Increment(n) % 2 == 1
    {
      if n % 2 == 0 {
        assert Increment(n) == n + 1;
      }
    }
  }

}
// Slide 7 Warning: controlling dafny's knowledge

module FPVerification_A12 {
  
    opaque function Increment(n: int): int {
      n + 1
    }
  
    lemma IncrementLarger()
      ensures forall n: int :: Increment(n) > n
    {
      reveal Increment();
    }
  
    lemma InrementEvenIsOdd()
      ensures forall n: int :: n % 2 == 0 ==> Increment(n) % 2 == 1
    {
      reveal Increment();
      forall n: int
        ensures n % 2 == 0 ==> Increment(n) % 2 == 1
      {
        if n % 2 == 0 {
        }
      }
    }
  
  }
  // Slide 8 Recall

module FPVerification_B123 {

  datatype List<T> =
    | Nil
    | Cons(head: T, tail: List)

  function Length<T>(l: List): nat {
    if l.Nil? then 0 else 1 + Length(l.tail)
  }

  function Append<T>(l1: List, l2: List): List {
    match l1
    case Nil => l2
    case Cons(e, l) => Cons(e, Append(l, l2))
  }

}
// Slide 9 Recursive programs? inductive proofs!

module FPVerification_B13 {

  import opened FPVerification_B123

  lemma AppendAssoc<T>(l1: List, l2: List, l3: List)
    ensures Append(Append(l1, l2), l3) == Append(l1, Append(l2, l3))
  {
    match l1
    case Nil =>
    case Cons(e, l) =>
      AppendAssoc(l, l2, l3); // this makes the proof clear to a human, but this line is not needed to convince Dafny
  }

}
// Slide 10 Structural induction: take 1

// Slide 11 Structural induction: take 2

// Slide 12 Structural induction: take 3

// Slide 13 Example proof by induction -- 1

// Slide 14 Example proof by induction -- 2

module FPVerification_B14 {

  import opened FPVerification_B123

  lemma AppendLength<T>(l1: List, l2: List)
    ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
  {
    match l1
    case Nil =>
    case Cons(e, l) =>
      AppendLength(l, l2); // Dafny doesn't actually need this line
  }

}
// Slide 15 Generalization -- 1

// Slide 16 Generalization -- 2

module FPVerification_B15 {
  
    import opened FPVerification_B123
  
    function LengthTr'<T>(l: List, acc: nat): nat {
      match l
      case Nil => acc
      case Cons(_, tail) => LengthTr'(tail, 1 + acc)
    }
  
    function LengthTr<T>(l: List): nat {
      LengthTr'(l, 0)
    }
  
  }
  // Slide 17 Generalization -- 3

module FPVerification_B16 {

  import opened FPVerification_B123
  import opened FPVerification_B15

  lemma LengthSame<T>(l: List)
    ensures Length(l) == LengthTr(l)

}
// Slide 18 Generalization -- 4

module FPVerification_B17 {

  import opened FPVerification_B123
  import opened FPVerification_B15

  lemma LengthSame'<T>(l: List, acc: nat)
    ensures acc + Length(l) == LengthTr'(l, acc)
  {
    match l
    case Nil =>
    case Cons(_, tail) =>
      LengthSame'(tail, acc + 1);
  }

}
// Slide 19 Generalization -- 5

// Slide 20 Mathematical functions

module DefiningFunctions_A1 {

  ghost function Increment(n: int): int

  lemma EssenceOfIncrement(n: int)
    ensures Increment(n) == n + 1

}
// Slide 21 Defining mathematical functions

module DefiningFunctions_A2 refines DefiningFunctions_A1 {

  ghost function Increment(n: int): int {
    n + 1
  }

}
// Slide 22 More consistent

// Slide 23 Termination -- easy case

module DefiningFunctions_A8 {
  
    function Sum(n: int): int
      decreases n // this line can be omitted, because Dafny will infer it
    {
      if n <= 0 then 0 else Sum(n - 1)
    }
  
  }
  // Slide 24 Termination -- harder case

module DefiningFunctions_A9 {
  
    function SumUpTo(counter: int, upTo: int): int
      decreases upTo - counter // here, the decreases clause is needed; Dafny will not infer it
    {
      if upTo <= counter then
        counter
      else
        counter + SumUpTo(counter + 1, upTo)
    }
  
  }
  // Slide 25 Ghost

module DefiningFunctions_A3 {
  
    predicate P<T>(m: T, n: T)
  
    ghost predicate Prop<T(!new)>(m: T) {
      exists n: T :: P(m, n)
    }
  
  }
  