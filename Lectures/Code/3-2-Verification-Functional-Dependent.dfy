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

// Slide 1 Functional code with pre/post conditions

// Slide 2 Postconditions -- 1

module CombiningProofAndFP_A1 {
  
    import opened CombiningProofAndFP_Pre
  
    function Append<T>(l1: List, l2: List): List
      ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
    {
      match l1
      case Nil => l2
      case Cons(e, l) => Cons(e, Append(l, l2))
    }
  
  }
  // Slide 3 Postconditions -- 2

module CombiningProofAndFP_A2 {
  
    import opened CombiningProofAndFP_Pre
  
    function Append<T>(l1: List, l2: List): List
      ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
    {
      match l1
      case Nil => l2
      case Cons(e, l) => Cons(e, Append(l, l2))
    }
  
  }
  // Slide 4 Postconditions -- 3

module CombiningProofAndFP_A3 {

  import opened CombiningProofAndFP_Pre

  function Append<T>(l1: List, l2: List): List
    ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
    ensures forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m

}
// Slide 5 Postconditions -- 4

module CombiningProofAndFP_A4 {
  
    import opened CombiningProofAndFP_Pre
  
    lemma SomeProperty()
      ensures forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m
  
    function Append<T>(l1: List, l2: List): List
      ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
      ensures forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m
    {
      SomeProperty();
      match l1
      case Nil => l2
      case Cons(e, l) => Cons(e, Append(l, l2))
    }
  
  }
  // Slide 6 Postconditions -- 5

module CombiningProofAndFP_A5 {
  
    import opened CombiningProofAndFP_Pre
  
    function Append<T>(l1: List, l2: List): List
      ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
      ensures forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m
    {
      assert forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m by {
        forall n: nat
          ensures n % 2 == 0 ==> exists m: nat :: n == 2 * m
        {
          if n % 2 == 0 {
            assert n == 2 * (n/2);
          }
        }
      }
      match l1
      case Nil => l2
      case Cons(e, l) => Cons(e, Append(l, l2))
    }
  
  }
  // Slide 7 Another example -- 6

module CombiningProofAndFP_A6 {

  import opened CombiningProofAndFP_Pre

  function LengthTr'<T>(l: List, acc: nat): nat
    ensures acc + Length(l) == LengthTr'(l, acc)
  {
    match l
    case Nil => acc
    case Cons(_, tail) => LengthTr'(tail, 1 + acc)
  }

  function LengthTr<T>(l: List): nat
    ensures Length(l) == LengthTr'(l, 0)
  {
    LengthTr'(l, 0)
  }

}
// Slide 8 Lemmas vs postconditions -- 7

module CombiningProofAndFP_A7 {
  
    import opened CombiningProofAndFP_Pre
  
    function Append<T(!new)>(l1: List, l2: List): List
      ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
      // ensures forall l3: List :: Append(Append(l1, l2), l3) == Append(l1, Append(l2, l3))
  
  }
  // Slide 9 Preconditions -- 8

module CombiningProofAndFP_A8 {
  
    import opened CombiningProofAndFP_Pre
  
    function At<T>(l: List, index: nat): T
      requires index < Length(l)
    {
      if index == 0 then l.head else At(l.tail, index - 1)
    }
  
  }
  // Slide 10 Preconditions -- 9

// Slide 11 Preconditions -- 10

module CombiningProofAndFP_A9 {
  
    import opened CombiningProofAndFP_Pre
    import opened CombiningProofAndFP_A8
  
    lemma AtProp<T(!new)>(l: List, idx: nat)
      requires idx < Length(l)
      ensures exists v: T :: At(l, idx) == v
    {
    }
  
  }
  // Slide 12 Preconditions and higher-order functions

module CombiningProofAndFP_A9a {
  
    function Hof<U, V>(f: U --> V, a: U): V
      requires f.requires(a)
    {
      f(a)
    }
  
  }
  // Slide 13 Requires function

// Slide 14 Should you mix code and proof? -- 1

// Slide 15 Should you mix code and proof? -- 2

// Slide 16 Should you mix code and proof? -- 3

// Slide 17 Subset types -- 1

module CombiningProofAndFP_A10 {
  
    type MyNat = n: int | 0 <= n
  
  }
  // Slide 18 Subset types -- 2

module CombiningProofAndFP_A11 {
  
    type MyNat = n: int | 0 <= n witness 4
  
  }
  // Slide 19 Subset types -- tip

module CombiningProofAndFP_A12 {
  
    method m(z: nat) {
      var x := z + 3; // No
      var y: nat := z + 3; // Yes
    }
  
  }
  // Slide 20 Subset types -- example

module CombiningProofAndFP_A13 {

  ghost predicate Associative<T(!new)>(BinOp: (T, T) -> T) {
    forall x: T, y: T, z: T :: BinOp(BinOp(x, y), z) == BinOp(x, BinOp(y, z))
  }

  ghost predicate Identity<T(!new)>(BinOp: (T, T) -> T, elt: T) {
    forall x: T :: BinOp(x, elt) == x
  }

  ghost predicate Inverse<T(!new)>(BinOp: (T, T) -> T, elt: T) {
    forall x: T :: exists y: T :: BinOp(x, y) == elt && BinOp(y, x) == elt 
  }

  type Group<!T(!new)> = S: ((T, T) -> T, T) | 
      && Associative(S.0) 
      && Identity(S.0, S.1)  
      && Inverse(S.0, S.1)
      witness *

}
