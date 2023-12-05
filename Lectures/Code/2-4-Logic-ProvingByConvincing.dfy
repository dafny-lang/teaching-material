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

// Slide 1 Recall

// Slide 2 Proofs that convince

// Slide 3 Summary 

// Slide 4 Lemmas and proofs

module BasicAutomation_Begin0 {
  
    lemma Example(x: int) 
      requires x % 2 == 0 
      ensures 2 * (x / 2) == x
  
  }
  // Slide 5 A notation for lemmas

// Slide 6 Proof challenges and automated theorem proving

module BasicAutomation_Begin1 {
  
    lemma Example(x: int) 
      requires x % 2 == 0 
      ensures 2 * (x / 2) == x
    {
    }
  
  }
  // Slide 7 From lemma and proof to challenges

// Slide 8 Automated theorem proving

// Slide 9 The trivial challenge

module BasicAutomation_A0 {
  
    lemma AndIntro<T1, T2, T3, T4>(x1: T1, x2: int, x3: int -> T4, P: bool, Q: T1 -> bool)
      requires Q(x1)
      requires P
      ensures P
    {}
  
  }
  // Slide 10 The essence of a challenge

// Slide 11 Basic challenges: conjunction

// Slide 12 Basic challenges: disjunction

// Slide 13 Basic challenges: negation

// Slide 14 Basic challenges: false

// Slide 15 Basic challenges: equivalence

// Slide 16 Basic challenges: existential quantifier

// Slide 17 Basic challenges: universal quantifier

// Slide 18 From proofs to challenges

module ProofMethod_A0 {
  
    import opened ProofMethod_Base 
  
    lemma {:verify false} Example<T>(x: T) 
      requires P(x) 
      ensures Q(x) 
    { 
      // T, x: T, P(x) |- Q(x)
  
      // ...
  
      // T, x: T, P(x), Q(x) |- Q(x)
    }
  
  }
  // Slide 19 Proof semantics: assert

module ProofMethod_Assert  {

  import opened ProofMethod_Base

  lemma {:verify false} Example<T>(x: T)
    requires P(x)
    ensures Q(x)
  {
    // T, x: T, P(x) |- Q(x)
    assert R(x) by {
      // T, x: T, P(x) |- R(x)
    } 
    // T, x: T, P(x), R(x) |- Q(x)
  }

}
// Slide 20 Proof semantics: assume

module ProofMethod_Assume  {

  import opened ProofMethod_Base

  lemma {:verify false} Conclusion<T>(x: T)
    requires P(x)
    ensures Q(x)
  {
    // T, x: T, P(x) |- Q(x)
    assume R(x);
    // T, x: T, P(x), R(x) |- Q(x)
  }

}
// Slide 21 Proof semantics: lemma call -- 1

module ProofMethod_Call1  {

  import opened ProofMethod_Base

  lemma Premise<T>(x: T)
    requires P(x)
    ensures R(x)

  lemma {:verify false} Conclusion<T>(x: T)
    requires P(x)
    ensures Q(x)
  {
    // T, x: T, P(x) |- Q(x)
    Premise<T>(x); // T, x: T, P(x) |- P(x)
    // T, x: T, P(x), R(x) |- Q(x)
  }

}
// Slide 22 Proof semantics: lemma call -- 2

module ProofMethod_Call2  {

  import opened ProofMethod_Base

  lemma Premise<T>(x: T)
    ensures P(x) ==> R(x)

  lemma {:verify false} Conclusion<T>(x: T)
    requires P(x)
    ensures Q(x)
  {
    // T, x: T, P(x) |- Q(x)
    Premise<T>(x);
    // T, x: T, P(x), P(x) ==> R(x) |- Q(x)
  }

}
// Slide 23 Proof semantics: lemma call -- 3

module ProofMethod_Call3  {

  import opened ProofMethod_Base

  lemma Premise<T>()
    ensures forall x: T :: P(x) ==> R(x)

  lemma {:verify false} Conclusion<T>(x: T)
    requires P(x)
    ensures Q(x)
  {
    // T, x: T, P(x) |- Q(x)
    Premise<T>();
    // T, x: T, P(x), forall x: T :: P(x) ==> R(x) |- Q(x)
  }

}
// Slide 24 Proof semantics: conditional statement -- 1

module ProofMethod_If1  {

  import opened ProofMethod_Base

  lemma {:verify false} Conclusion<T>(x: T)
    requires P(x)
    ensures Q(x)
  {
    // T, x: T, P(x) |- Q(x)
    if R(x) {
      // T, x: T, P(x), R(x) |- S(x)
    }
    // T, x: T, P(x), R(x) ==> S(x) |- Q(x)
  }

}
// Slide 25 Proof semantics: conditional statement -- 2

module ProofMethod_If2  {

  import opened ProofMethod_Base

  lemma Premise<T>(x: T)
    requires P(x)
    ensures R(x)

  lemma {:verify false} Conclusion<T>(x: T)
    ensures P(x) ==> Q(x)
  {
    // T , x: T |- P(x) ==> Q(x)
    if P(x) {
      Premise(x); // T, x: T, P(x) |- P(x)
      // T, x: T, P(x) |- Q(x)
    }
    // T, x: T, P(x) ==> R(x) |- P(x) ==> Q(x)
  }

}
// Slide 26 Proof semantics: forall statement

module ProofMethod_Forall  {

  import opened ProofMethod_Base

  lemma {:verify false} Conclusion<T>(x: T)
    requires P(x)
    ensures Q(x)
  {
    // T, x: T, P(x) |- Q(x)
    forall x: T
      ensures R(x)
    {
      // T , x: T, P(x) |- R(x)
    }
    // T, x: T, P(x), forall x: T :: R(x) |- Q(x)
  }

}
// Slide 27 Proof semantics: variable choice

module ProofMethod_Choice  {

  import opened ProofMethod_Base

  lemma {:verify false} Conclusion<T>()
    requires exists y: T :: P(y)
    ensures A
  {
    // T, exists x: T :: P(x) |- A
    var y: T :| P(y); 
    // T, y: T, P(y) |- A
  }

}
// Slide 28 Proof semantics: variable assigment

module ProofMethod_Assignment  {

  import opened ProofMethod_Base

  lemma {:verify false} Conclusion<T>(x: T)
    ensures A
  {
    // T, x: T |- A
    var y: T := x; 
    // T, x: T, y: T, y == x |- A
  }

}
// Slide 29 Example

module ProofMethod_B3  {

  import opened ProofMethod_Base

  lemma Premise<T>(x: T)
    requires P(x)
    ensures Q(x)

  lemma {:verify false} Conclusion<T>()
    ensures forall x: T :: P(x) ==> Q(x)
  {
    // T |- forall x: T :: P(x) ==> Q(x)
    forall x: T
      ensures P(x) ==> Q(x)
    {
      // T , x: T |- P(x) ==> Q(x)
      if P(x) {
        Premise(x); // T, x: T, P(x) |- P(x)
        // T, x: T, P(x) |- Q(x)
      }
      // T, x: T, P(x) ==> Q(x) |- P(x) ==> Q(x)
    }
    // T , forall x: T :: P(x) ==> Q(x) |- forall x: T :: P(x) ==> Q(x)
  }

}
// Slide 30 Structuring a proof

// Slide 31 Incrementally writing a proof with assume

module ProofMethod_Assume1 {
  
    import opened ProofMethod_Base
  
    lemma Example() 
    {
      // ...
      assume A; // TODO
      // ...
    }
  
  }
  // Slide 32 Removing an assumption: assert

module ProofMethod_Assume2 {

  import opened ProofMethod_Base

  lemma Example() 
  {
    // ...
    assert A by {
      assume false; // TODO
    }
    // ...
  }

}
// Slide 33 Removing an assumption: lemma call

module ProofMethod_Assume3 { 

  import opened ProofMethod_Base

  lemma Prior() 
    ensures A

  lemma Example() 
  {
    // ...
    Prior();
    // ...
  }

}
// Slide 34 How to prove: conjunction -- procedural

module ProofMethod_ConjunctionIntro {

  import opened ProofMethod_Base

  lemma Example()
    ensures A && B
  {
    // |- A && B
    assume A; 
    // A |- A && B
    assume B; 
    // A , B |- A && B
  }

}
// Slide 35 How to prove: conjunction -- procedural to declarative

module ProofMethod_ConjunctionLeft {

  import opened ProofMethod_Base 

  lemma Example()
    ensures A && B
  {
    // |- A && B
    assume A && B;
    // A && B |- A && B
  }

}
// Slide 36 How to prove: conjunction -- declarative

module ProvingByConvincing_HTP1A {
  import opened ProvingByConvincing_PreReq     
  lemma Goal()              
    ensures A && B      
  {                        
    assume A && B;
  }                        
}
module ProvingByConvincing_HTP1B {
  import opened ProvingByConvincing_PreReq     
  lemma Goal()              
    ensures A && B      
  {                        
    assert A && B by {
      assume A;
      assume B;
    }
  }                        
}
// Slide 37 How to prove: disjunction, procedural -- 1

module ProofMethod_DisjunctionIntroLeft {

  import opened ProofMethod_Base

  lemma Example()
    ensures A || B
  {
    // |- A || B
    assume A; 
    // A |- A || B
  }

}
// Slide 38 How to prove: disjunction, procedural -- 2

module ProofMethod_DisjunctionIntroRight {

  import opened ProofMethod_Base

  lemma Example()
    ensures A || B
  {
    // |- A || B
    assume B; 
    // B |- A || B
  }

}
// Slide 39 How to prove: disjunction, declarative -- 1

module ProvingByConvincing_HTP3A {

  import opened ProvingByConvincing_PreReq     

  lemma before()     
    ensures A || B     
  {     
    assume A || B;
  }     

}
module ProvingByConvincing_HTP3B {

  import opened ProvingByConvincing_PreReq     

  lemma after()     
    ensures A || B     
  {     
    assert A || B by {
      assume A;
    }
  }     

}
// Slide 40 How to prove: disjunction, declarative -- 2

module ProvingByConvincing_HTP3C {

  import opened ProvingByConvincing_PreReq     

  lemma after()     
    ensures A || B     
  {     
    assert A || B by {
      assume B;
    }
  }     

}
// Slide 41 How to prove: disjunction, declarative -- 3

module ProvingByConvincing_HTP3D {

  import opened ProvingByConvincing_PreReq     

  lemma after()     
    ensures A || B     
  {     
    assert A || B by {
      if !A {
        assume B;
      }
    }
  }     

}
// Slide 42 How to prove: disjunction, declarative -- 4

module ProvingByConvincing_HTP3E {

  import opened ProvingByConvincing_PreReq     

  lemma after()     
    ensures A || B     
  {     
    assert A || B by {
      if !B {
        assume A;
      }
    }
  }     

}
// Slide 43 How to prove: implication, procedural

module ProofMethod_ImplicationIntro { 

  import opened ProofMethod_Base

  lemma Example()
    ensures A ==> B
  {
    // |- A ==> B
    if A {
      assume B;
    }
    // A ==> B |- A ==> B
  }

}
// Slide 44 How to prove: implication, declarative -- 1

module ProvingByConvincing_HTP2A {

  import opened ProvingByConvincing_PreReq     

  lemma before()     
    ensures A ==> B     
  {     
    assume A ==> B;
  }     

}
module ProvingByConvincing_HTP2B {

  import opened ProvingByConvincing_PreReq     

  lemma after()     
    ensures A ==> B     
  {     
    assert A ==> B by {
      if A {
        assume B;
      }
    }
  }     

}
// Slide 45 How to prove: implication, declarative -- 2

module ProvingByConvincing_HTP2C {

  import opened ProvingByConvincing_PreReq     

  lemma after()     
    ensures A ==> B     
  {     
    assert A ==> B by {
      if !B {
        assume !A;
      }
    }
  }     

}
// Slide 46 How to prove: negation procedural

module ProofMethod_NegationIntro { 

  import opened ProofMethod_Base

  lemma Example()
    ensures !A
  {
    // |- !A
    if A {
      assume false;
    }
    // A ==> false |- !A
  }

}
// Slide 47 How to prove: negation, declarative

module ProvingByConvincing_HTP7A {

  import opened ProvingByConvincing_PreReq     

  lemma before()     
    ensures !A     
  {     
    assume !A;
  }     

}
module ProvingByConvincing_HTP7B {

  import opened ProvingByConvincing_PreReq     

  lemma before()     
    ensures !A     
  {     
    assert !A by {
      if A {
        assume false;
      }
    }
  }     

}
// Slide 48 How to prove: universal quantification, procedural

module ProofMethod_UniversalIntro { 

  import opened ProofMethod_Base

  lemma Exampl<T>()
    ensures forall x: T :: P(x)
  {
    // |- forall x: T :: P(x)
    forall x: T
      ensures P(x)
    {
      assume P(x);
    }
    // forall x: T :: P(x) |- forall x: T :: P(x)
  }

}
// Slide 49 How to prove: universal quantification, declarative

module ProvingByConvincing_HTP5A {

  import opened ProvingByConvincing_PreReq2     

  lemma before()     
    ensures forall x: nat :: P(x)     
  {     
    assume forall x: nat :: P(x);
  }     

}
module ProvingByConvincing_HTP5B {

  import opened ProvingByConvincing_PreReq2     

  lemma before()     
    ensures forall x: nat :: P(x)     
  {     
    assert forall x: nat :: P(x) by {
      forall x: nat
        ensures P(x)
      {
        assume P(x);
      }
    }
  }     

}
// Slide 50 How to prove: existential quantification, procedural

module ProofMethod_ExistentialIntro { 

  import opened ProofMethod_Base

  lemma Example<T>(c: T)
    ensures exists x: T :: P(x)
  {
    // |- exists x: T :: P(x)
    assume P(c);
    // exists x: T :: P(x) |- exists x: T :: P(x)
  }

}
// Slide 51 How to prove: existential quantification, declarative

module ProvingByConvincing_HTP6A {

  import opened ProvingByConvincing_PreReq2     

  lemma before()     
    ensures exists x: nat :: P(x)     
  {     
    assume exists x: nat :: P(x);
  }     

}
module ProvingByConvincing_HTP6B {

  import opened ProvingByConvincing_PreReq2     

  lemma before()     
    ensures exists x: nat :: P(x)     
  {     
    assert exists x: nat :: P(x) by {
      assume P(c);
    }
  }     

}
// Slide 52 How to use: implication

module ProofMethod_ImplicationElim { 

  import opened ProofMethod_Base

  lemma Example()
    requires A ==> B
    ensures B
  {
    // A ==> B |- B
    assume A;
    // A ==> B, A |- B
  }

}
// Slide 53 How to use: disjunction

module ProofMethod_DisjunctionElim { 

  import opened ProofMethod_Base 

  lemma Example() 
    requires A || B 
    ensures C
  {
    // A || B |- C
    if A {
      assume C;
    }
    // A || B, A ==> C |- C 
    if B {
      assume C;
    }
    // A || B, A ==> C, B ==> C |- C
  }

}
// Slide 54 How to use: negation

module ProofMethod_NegationElim {

 import opened ProofMethod_Base 

  lemma Example() 
    requires !A
    ensures false 
    {
      // !A |- false 
      assume A; 
      // !A, A |- false
    }

}
// Slide 55 How to use: existential

module ProofMethod_ExistentialElim {

  import opened ProofMethod_Base 

  lemma Example<T>() 
    requires exists c: T :: P(c)
    ensures C 
  {
    // exists c: T :: P(c) |- C 
    assume forall x: T :: P(x) ==> C;
    // exists c: T :: P(c), forall x: T :: P(x) ==> C |- C 
    var c: T :| P(c);
    // exists c: T :: P(c), c:T, P(c), forall x: T :: P(x) ==> C |- C 
  }

}
// Slide 56 How to use: congruence of propositions

module ProvingByConvincing_HTUBase {

  import opened ProvingByConvincing_PreReq     

  lemma Goal()     
    ensures A     
  {     
    assume A;
  }     

}
module ProvingByConvincing_HTU6B {

  import opened ProvingByConvincing_PreReq     

  lemma av()     
    ensures A     
  {     
    assert A by {
      assume A == B;
      assume B;
    }
  }     


}
// Slide 57 How to use: congruence of terms

module ProvingByConvincing_HTUBase' {

  import opened ProvingByConvincing_PreReq2     

  lemma Goal()     
    ensures P(c)     
  {     
    assume P(c);
  }     

}
module ProvingByConvincing_HTU6C {

  import opened ProvingByConvincing_PreReq2     
  const d: nat     

  lemma av()     
    ensures P(c)     
  {     
    assert P(c) by {
      assume c == d;
      assume P(d);
    }
  }     


}
// Slide 58 Detailed example

// Slide 59 In english

// Slide 60 Procedural -- 1

module Mathematics_New1 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y

}
// Slide 61 Procedural -- 2

module Mathematics_New2 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    // |- GOAL
    assume false; // TODO












    
    // false |- GOAL
  }

}
// Slide 62 Procedural -- 3

module Mathematics_New3 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    // |- GOAL
    assume forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y; // TODO













    // GOAL |- GOAL
  }

}
// Slide 63 Procedural -- 4

module Mathematics_New4 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    // |- GOAL
    forall x: nat
      ensures x % 2 == 0 ==> exists y: nat :: x == 2 * y
    {
      // x: nat |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
      assume false; // TODO









      // x: nat, false |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
    }
    // GOAL |- GOAL
  }

}
// Slide 64 Procedural -- 5

module Mathematics_New5 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    // |- GOAL
    forall x: nat
      ensures x % 2 == 0 ==> exists y: nat :: x == 2 * y
    {
      // x: nat |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
      assume x % 2 == 0 ==> exists y: nat :: x == 2 * y; // TODO








      // x: nat, x % 2 == 0 ==> exists y: nat :: x == 2 * y 
      //                  |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
    }
    // GOAL |- GOAL
  }

}
// Slide 65 Procedural -- 6

module Mathematics_New6 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    // |- GOAL
    forall x: nat
      ensures x % 2 == 0 ==> exists y: nat :: x == 2 * y
    {
      // x: nat |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
      if x % 2 == 0 {
        // x: nat, x % 2 == 0 |- exists y: nat :: x == 2 * y
        assume false; // TODO




        // x: nat, x % 2 == 0, false |- exists y: nat :: x == 2 * y
      }
      // x: nat, x % 2 == 0 ==> exists y: nat :: x == 2 * y 
      //                  |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
    }
    // GOAL |- GOAL
  }

}
// Slide 66 Procedural -- 7

module Mathematics_New7 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    // |- GOAL
    forall x: nat
      ensures x % 2 == 0 ==> exists y: nat :: x == 2 * y
    {
      // x: nat |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
      if x % 2 == 0 {
        // x: nat, x % 2 == 0 |- exists y: nat :: x == 2 * y
        assert exists y: nat :: x == 2 * y by {
          // x: nat, x % 2 == 0 |- exists y: nat :: x == 2 * y
          assume false; // TODO
          // x: nat, x % 2 == 0, false |- exists y: nat :: x == 2 * y
        }
        // x: nat, x % 2 == 0, exists y: nat :: x == 2 * y |- exists y: nat :: x == 2 * y
      }
      // x: nat, x % 2 == 0 ==> exists y: nat :: x == 2 * y 
      //                  |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
    }
    // GOAL |- GOAL
  }

}
// Slide 67 Procedural -- 8

module Mathematics_New8 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    // |- GOAL
    forall x: nat
      ensures x % 2 == 0 ==> exists y: nat :: x == 2 * y
    {
      // x: nat |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
      if x % 2 == 0 {
        // x: nat, x % 2 == 0 |- exists y: nat :: x == 2 * y
        assert exists y: nat :: x == 2 * y by {
          // x: nat, x % 2 == 0 |- exists y: nat :: x == 2 * y
          assert x == 2 * (x / 2);
          // x: nat, x % 2 == 0, exists y: nat :: x == 2 * y |- exists y: nat :: x == 2 * y
        }
        // x: nat, x % 2 == 0, exists y: nat :: x == 2 * y |- exists y: nat :: x == 2 * y
      }
      // x: nat, x % 2 == 0 ==> exists y: nat :: x == 2 * y 
      //                  |- x % 2 == 0 ==> exists y: nat :: x == 2 * y
    }
    // GOAL |- GOAL
  }

}
// Slide 68 Declarative -- 1

module Mathematics_Dec1 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y

}
// Slide 69 Declarative -- 2

module Mathematics_Dec2 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    assume false; // TODO
  }

}
// Slide 70 Declarative -- 3

module Mathematics_Dec3 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    forall x: nat
      ensures x % 2 == 0 ==> exists y: nat :: x == 2 * y
    {
      assume false; // TODO
    }
  }

}
// Slide 71 Declarative -- 4

module Mathematics_Dec4 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    forall x: nat
      ensures x % 2 == 0 ==> exists y: nat :: x == 2 * y
    {
      if x % 2 == 0 {
        assume false; // TODO
      }
    }
  }

}
// Slide 72 Declarative -- 5

module Mathematics_Dec5 {

  lemma s1()
    ensures forall x: nat :: x % 2 == 0 ==> exists y: nat :: x == 2 * y
  {
    forall x: nat
      ensures x % 2 == 0 ==> exists y: nat :: x == 2 * y
    {
      if x % 2 == 0 {
        assert x == 2 * (x / 2);
      }
    }
  }

}
// Slide 73 Proofs that calculate

// Slide 74 Back-of-the-envelope calculations

module ProvingByComputing_A16 {
  
    lemma OddFactor(n: nat)
      requires n % 2 == 1
      ensures exists m: nat :: n == m * 2 + 1
    {
      assert n == n/2 * 2 + 1;
    }
  
  }
  module ProvingByComputing_A17 {
  
    lemma OffFactorComputed(n: nat) returns (m: nat)
      requires n % 2 == 1
      ensures n == m * 2 + 1
    {
      m := n/2;
    }
  
  }
  