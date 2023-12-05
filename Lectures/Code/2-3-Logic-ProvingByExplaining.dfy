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

// Slide 1 Dafny: a proof assistant

module ProvingByExplaining_Start {
  
    lemma Proposition()
      ensures forall m: int, n: int :: m > 0 && n > m ==> m + n > 0
  
  }
  // Slide 2 Dafny: an auto-active proof assistant

module ProvingByExplaining_AutoActive {
  
    lemma AutoActive()
      ensures forall m: int, n: int :: m + n == n + m
    {
    }
  
  }
  // Slide 3 Writing proofs

// Slide 4 Proofs that explain

// Slide 5 Proving by explaining

module ProvingByExplaining_EvenModule {
  
    ghost predicate Even(n: nat)
  
    ghost predicate Odd(n: nat)
  
    lemma EvenP()
      ensures forall n: nat :: Even(n) == exists m: nat :: n == 2 * m
  
    lemma OddP()
      ensures forall n: nat :: Odd(n) == !Even(n)
  
    lemma SuccOddIsEven()
      ensures forall n: nat :: Odd(n) ==> Even(n + 1)
  
  }
  // Slide 6 What does dafny know?

// Slide 7 Proof statements

// Slide 8 Asserting and calling propositions

module ProvingByExplaining_SuccOddIsEven1 {

  import opened ProvingByExplaining_EvenModule

  lemma SuccOddIsEven()
    ensures forall n: nat :: Odd(n) ==> Even(n + 1)
  {

    EvenP();
    OddP();

    assert forall n: nat :: n % 2 == 0 ==> n == 2 * (n / 2);
    assert forall n: nat :: n == 2 * (n / 2) ==> Even(n);
    assert forall n: nat :: Odd(n) ==> n % 2 == 1;
    assert forall n: nat :: n % 2 == 1 ==> (n + 1) % 2 == 0;

  }

}
// Slide 9 Fixing arbitrary values

module ProvingByExplaining_SuccOddIsEven2 {

  import opened ProvingByExplaining_EvenModule

  lemma SuccOddIsEven(n: nat)
    ensures Odd(n) ==> Even(n + 1)
  {

    EvenP();
    OddP();

    assert forall n: nat :: n % 2 == 0 ==> n == 2 * (n / 2);
    assert forall n: nat :: n == 2 * (n / 2) ==> Even(n);
    assert Odd(n) ==> n % 2 == 1;
    assert Odd(n) ==> (n + 1) % 2 == 0;

  }

}
// Slide 10 Fixing assumptions

module ProvingByExplaining_SuccOddIsEven3 {
  
    import opened ProvingByExplaining_EvenModule
  
    lemma SuccOddIsEven(n: nat)
      requires Odd(n)
      ensures Even(n + 1)
    {
  
      EvenP();
      OddP();
      
      assert forall n: nat :: n % 2 == 0 ==> n == 2 * (n / 2);
      assert forall n: nat :: n == 2 * (n / 2) ==> Even(n);
      assert n % 2 == 1;
      assert (n + 1) % 2 == 0;
    
    }
  
  }
  // Slide 11 Structuring a proof in lemmas

module ProvingByExplaining_SuccOddIsEven4 {
  
    import opened ProvingByExplaining_EvenModule
  
    lemma DivBy2IsEven()
      ensures forall n: nat :: n % 2 == 0 ==> Even(n)
    {
      EvenP(); OddP();
      assert forall n: nat :: n % 2 == 0 ==> n == 2 * (n / 2);
    }
  
    lemma SuccOddIsEven(n: nat)
      requires Odd(n)
      ensures Even(n + 1)
    {
      OddP();
      DivBy2IsEven();
      
      assert n % 2 == 1;
      assert (n + 1) % 2 == 0;
    }
  
  }
  // Slide 12 Reasoning incrementally

module Mathematics_A1_0 {
  
    import opened Mathematics_Pre
  
    lemma Prop()
      ensures forall n: nat :: Even(n) ==> Even(n + 2)
    {
      assume false; // TODO
    }
  
  }
  // Slide 13 Universal introduction

module Mathematics_A1_1 {
  
    import opened Mathematics_Pre
  
    lemma Prop()
      ensures forall n: nat :: Even(n) ==> Even(n + 2)
    {
      forall n: nat
        ensures Even(n) ==> Even(n + 2)
      {
        assume false; // TODO
      }
    }
  
  }
  // Slide 14 Implication introduction

module Mathematics_A1_2 {
  
    import opened Mathematics_Pre
  
    lemma Prop()
      ensures forall n: nat :: Even(n) ==> Even(n + 2)
    {
      forall n: nat
        ensures Even(n) ==> Even(n + 2)
      {
        if Even(n) {
          assume false; // TODO
        }
      }
    }
  
  }
  // Slide 15 Skolemization

module Mathematics_A1_3 {
  
    import opened Mathematics_Pre
  
    lemma Prop()
      ensures forall n: nat :: Even(n) ==> Even(n + 2)
    {
      forall n: nat
        ensures Even(n) ==> Even(n + 2)
      {
        if Even(n) {
          var a: nat :| n == 2 * a;
          assume false; // TODO
        }
      }
    }
  
  }
  // Slide 16 Providing a witness

module Mathematics_A1_4 {
  
    import opened Mathematics_Pre
  
    lemma Prop()
      ensures forall n: nat :: Even(n) ==> Even(n + 2)
    {
      forall n: nat
        ensures Even(n) ==> Even(n + 2)
      {
        if Even(n) {
          var a: nat :| n == 2 * a;
          var b: nat := 2 * (a + 1);
        }
      }
    }
  
  }
  // Slide 17 Proof methods

// Slide 18 Proof by contradiction

module Mathematics_A16 {
  
    import opened Mathematics_Pre
  
    lemma ProofByContradiction(n: nat)
      requires Even(n)
      ensures !exists m: nat :: n == 2 * m + 1
    {
  
      var m1: nat :| n == 2 * m1;
  
      if exists m: nat :: n == 2 * m + 1 {
  
        var m2: nat :| n == 2 * m2 + 1;
        assert false;
  
      }
  
    }
  
  }
  // Slide 19 Proof by case analysis

module Mathematics_A17 {
  
    import opened Mathematics_Pre
  
    lemma ProofByCaseAnalysis(n: nat)
      ensures Even(n) || Odd(n)
    {
  
      if n % 2 == 0 { assert n == 2 * (n / 2); }
  
      if n % 2 == 1 { assert n == (2 * (n / 2)) + 1; }
  
    }
  
  }
  // Slide 20 Proof by induction

// Slide 21 Pencil and paper proof by induction

// Slide 22 Dafny proof by induction

module Mathematics_A18 {
  
    import opened Mathematics_Pre
  
    lemma ProofByInduction(n: nat)
      requires n % 2 == 0
      ensures Even(n)
    {
  
      if n == 0 {
  
        assert n == 2 * 0;
  
      } else {
  
        assert (n - 2) % 2 == 0;
        ProofByInduction(n - 2);
        var m: nat :| n - 2 == 2 * m;
        assert n == 2 * m + 2;
        assert n == 2 * (m + 1);
  
      }
    }
  
  }
  