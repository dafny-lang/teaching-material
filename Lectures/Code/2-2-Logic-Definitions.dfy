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

// Slide 1 Axioms

module FormalizingMathematics_Axiom {
  
    lemma Axiom()
      ensures forall m: int, n: int :: m + n == n + m
  
  }
  // Slide 2 Defining mathematical objects

// Slide 3 Defining constants

module DefiningFunctions_A0 {
  
    ghost const x: int
  
    lemma EssenceOfX()
      ensures x == 0
  
  }
  module DefiningFunctions_A0' refines DefiningFunctions_A0 {
  
    ghost const x: int := 0
  
  }
  // Slide 4 Defining simple functions

module DefiningFunctions_A1 {
  
    ghost function Increment(n: int): int
  
    lemma EssenceOfIncrement(n: int)
      ensures Increment(n) == n + 1
  
  }
  module DefiningFunctions_A2 refines DefiningFunctions_A1 {
  
    ghost function Increment(n: int): int {
      n + 1
    }
  
  }
  // Slide 5 Defining functions with quantifiers

module DefiningFunctions_MathDef {
  
    ghost predicate Valid(P: int -> bool) {
      forall x: int :: P(x)
    }
  
  }
  // Slide 6 Defining partial functions

module DefiningFunctions_Div1 {
  
    ghost function Divide(m: int, n: int): int
  
    lemma EssenceOfDivide(m: int, n: int)
      requires n != 0
      ensures Divide(m, n) == m / n
  
  }
  module DefiningFunctions_Div2 {
  
    ghost function Divide(m: int, n: int): int
      requires n != 0
    {
      m / n
    }
  
  }
  // Slide 7 Defining functions by description

module DefiningFunctions_A4 {
  
    predicate P<T>(m: T, n: T)
  
    ghost predicate Prop<T(!new)>(m: T) {
      exists n: T :: P(m, n)
    }
  
    ghost function F<T>(m: T): T
      requires Prop(m)
    {
      var n :| P(m, n);
      n
    }
  
  }
  // Slide 8 Axiomatizing recursive functions

module DefiningFunctions_Rec1 {
  
    ghost function Factorial(n: int): int
  
    lemma FactorialProp0()
      ensures Factorial(0) == 1
  
    lemma FactorialProp1(n: int)
      requires n > 0
      ensures Factorial(n) == n * Factorial(n - 1)
  
  }
  // Slide 9 Danger of axiomatizing recursive functions

module DefiningFunctions_RecBogus {
  
    ghost function Factorial(n: int): int
  
    lemma FactorialBogus1(n: int)
      ensures Factorial(n) == n * Factorial(n - 1)
  
    lemma FactorialBogus2(n: int)
      ensures Factorial(n) == n * Factorial(n)
  
  }
  // Slide 10 Defining recursive functions

module DefiningFunctions_Rec2 {
  
    ghost function Factorial(n: int): int 
      requires 0 <= n
    {
      if n == 0 then 1 else Factorial(n - 1)
    }
  
  }
  // Slide 11 Existence of recursive functions

// Slide 12 Termination --- easy case

module DefiningFunctions_A8 {
  
    function Sum(n: int): int
      decreases n // this line can be omitted, because Dafny will infer it
    {
      if n <= 0 then 0 else Sum(n - 1)
    }
  
  }
  // Slide 13 Termination --- harder case

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
  // Slide 14 Defining recursive functions: beyond well-founded ordering

module DefiningFunctions_A5Test {
  
    predicate Closure<T(!new)>(Relation: (T, T) -> bool, x: T, y: T)
  
    lemma ClosureProp1<T(!new)>(Relation: (T, T) -> bool, x: T)
      ensures Closure(Relation, x, x)
  
    lemma ClosureProp2<T(!new)>(Relation: (T, T) -> bool, x: T, y: T)
      ensures exists z: T :: Relation(x, z) && Closure(Relation, z, y)
  
  }
  // Slide 15 Least predicates

module DefiningFunctions_A5 {
  
    least predicate Closure<T(!new)>(Relation: (T, T) -> bool, x: T, y: T) {
      || x == y
      || (exists z: T :: Relation(x, z) && Closure(Relation, z, y))
    }
  
  }
  // Slide 16 Definition of theories

module DefiningFunctions_Peano {
  
    type Peano(0) 
  
    ghost const Zero: Peano 
  
    ghost function Succ(n: Peano): Peano 
  
    lemma PeanoInjectivity(m: Peano, n: Peano)
      requires Succ(m) == Succ(n)
      ensures m == n
  
    lemma PeanoDiff(n: Peano)
      ensures Succ(n) != Zero 
  
    lemma PeanoExhaustive(n: Peano)
      ensures n == Zero || exists m: Peano :: n == Succ(m)
  
    lemma InductionPrinciple(P: Peano -> bool) 
      requires P(Zero) 
      requires forall n: Peano :: P(n) ==> P(Succ(n))
      ensures forall n: Peano :: P(n)
  }
  // Slide 17 Definition

module DefiningFunctions_PeanoADT {
  
    datatype Peano = 
      | Zero 
      | Succ(Peano)
  
  }
  