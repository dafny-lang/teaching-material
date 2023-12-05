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

// Slide 1 Dafny as a proof assistant

// Slide 2 Theories

// Slide 3 Type symbols

module FormalizingMathematics_SymbolTypeNat {
  
    type NaturalNumber(00)
  
  }
  module FormalizingMathematics_SymbolTypeList {
  
    type NaturalNumber(00)
  
  }
  // Slide 4 Constant symbols

module FormalizingMathematics_ConstantSymbol {
  
    import opened FormalizingMathematics_SymbolTypeNat
  
    ghost const zero: NaturalNumber
  
  }
  // Slide 5 Function symbols

module FormalizingMathematics_FunctionSymbol {
  
    import opened FormalizingMathematics_SymbolTypeNat
  
    ghost function Successor(n: NaturalNumber): NaturalNumber
  
  }
  // Slide 6 Predicate symbols

module FormalizingMathematics_PredicateSymbol {
  
    import opened FormalizingMathematics_SymbolTypeNat
  
    ghost predicate Less(n: NaturalNumber, m: NaturalNumber)
  
  }
  // Slide 7 Lemmas

module ProvingByExplaining_Start {
  
    lemma Proposition()
      ensures forall m: int, n: int :: m > 0 && n > m ==> m + n > 0
  
  }
  // Slide 8 Lemma schema

module FormalizingMathematics_Schema1 {
  
    lemma Prop() 
      ensures forall x: int :: x % 2 == 0 ==> (x / 2) * 2 == x 
  
  }
  // Slide 9 Schemas with parameters

module FormalizingMathematics_Schema2' {
  
    lemma Prop<T>(x: T) 
      ensures x == x
  
  }
  // Slide 10 Schemas with preconditions

module FormalizingMathematics_Schema3 {
  
    lemma Prop(x: int) 
      requires x % 2 == 0
      ensures (x / 2) * 2 == x 
  
  }
  // Slide 11 Type test

module FunctionalProgramming_Example {
  
    predicate IntPlus3IsInt(n: int) { (n + 3) is int }
  
  }
  // Slide 12 Basic expressions

module Expressions_SimpleExpressions {

  predicate ConditionalExpression<T>(bexpr: bool, expr1: T, expr2: T)  { 
    (if bexpr then expr1 else expr2) is T
  }

  predicate LetBinding<U, V>(expr1: U, expr2: V) { (var x := expr1; expr2) is V }

  predicate Tuple<T, U, V>(t: T, u: U, v: V) { (t, u, v) is (T, U, V) }

  predicate TupleAccess0<T, U, V>(tup: (T, U, V)) { tup.0 is T }

  predicate TupleAccess1<T, U, V>(tup: (T, U, V)) { tup.1 is U }

  predicate TupleAccess2<T, U, V>(tup: (T, U, V)) { tup.2 is V }

}
// Slide 13 Anonymous functions and application

module Expressions_FunctionExpressions {

  predicate LambdaAbstraction<U, V>(expr: V) { ((x: U) => expr) is U -> V }

  predicate Application<U, V>(fun: U -> V, arg: U) { fun(arg) is V }

}
// Slide 14 Propositions != expressions

// Slide 15 Propositional logic

module Booleans_Theory {
  
    // Constants
    lemma False()
      ensures false 
    lemma True()
      ensures true 
  
    // Predicates
    lemma Conjunction(a: bool, b: bool)
      ensures a && b 
    lemma Disjunction(a: bool, b: bool)
      ensures a || b 
    lemma Implication(a: bool, b: bool)
      ensures a ==> b 
    lemma Explication(a: bool, b: bool)
      ensures a <== b 
    lemma Equivalence(a: bool, b: bool)
      ensures a <==> b 
    lemma Negation(a: bool)
      ensures !a 
  
  }
  // Slide 16 First-order logic

module Booleans_PredLogic {
  
    type T
    
    ghost predicate P(x: T)
  
    lemma PredicateLogicConnectives()
      ensures (forall x: T :: P(x)) is bool
      ensures (exists x: T :: P(x)) is bool
  
  }
  // Slide 17 Second-order logic

module FormalizingMathematics_PropositionsFour {
  
    lemma SecondOrder()
      ensures forall P: int -> bool :: forall x: int :: P(x) || !P(x)
  
  }
  // Slide 18 Higher-order logic

module FormalizingMathematics_PropositionsFive {
  
    lemma ThirdOrder()
      ensures forall P2: (int -> bool) -> bool :: forall P1: int -> bool :: P2(P1) || !P2(P1)
  
  }
  // Slide 19 Impredicativity of propositions

module FormalizingMathematics_Impredicativity {
  
    import opened FormalizingMathematics_Pre
  
    lemma Impredicative()
      ensures forall x: T :: forall P: T -> bool :: P(x)
  
  }
  // Slide 20 Predicativity of polymorphism

module FormalizingMathematics_Predicativity {
  
    type List<X>
  
    function F<T>(x: T): T {
      x
    }
  
    function G(): List -> List {  // expands to:  function G<_T0>(): List<_T0> -> List<_T0>
      F<List>                     // expands to:  F<List<_T0>>
    }
  
  }
  // Slide 21 Partiality

module FormalizingMathematics_Partial1 {
  
    lemma {:verify false} Partial() 
      ensures forall x: int :: x * 1/x == x 
  
  }
  // Slide 22 Partiality and proofs

module FormalizingMathematics_Partial2 {
  
    lemma Partial() 
      ensures forall x: int :: x != 0 ==> x / x == 1
  
  }
  // Slide 23 Description

module FormalizingMathematics_Description { 
  
    predicate P(x: int)
  
    lemma HilbertEpsilon() 
      requires forall x: int :: P(x)
      ensures var x: int :| P(x); true 
  
  }
  // Slide 24 Referential transparency

module FormalizingMathematics_RefTrans {
  
    lemma NotReferentiallyTransparent()
      ensures (var x: int :| true; x) == (var x: int :| true; x)
  
  }
  // Slide 25 Subtypes

module FormalizingMathematics_SubsetType {
  
    type T
  
    predicate P(x: T) 
  
    type U = x: T | P(x)
      witness *
  
  }
  // Slide 26 Empty subset types

module FormalizingMathematics_SubsetType2 {
  
    type T(00)
  
    ghost const k: T
  
    type U = x: T | true
      ghost witness k
  
  }
  // Slide 27 Subtyping

module FormalizingMathematics_Subtyping0 {
  
    type T 
  
    predicate P1(x: T)
  
    type U = x: T | P1(x) witness *
  
    predicate P2(x: U)
  
    type V = x: U | P2(x) witness *
  
  }
  // Slide 28 Subtyping for functions

module FormalizingMathematics_Subtyping1 refines FormalizingMathematics_Subtyping0 {
  
    lemma Subtyping(h: (V -> T) -> bool, f: U -> U)
      ensures h(f) 
  
  }
  // Slide 29 Covariant subtyping for type parameters

module FormalizingMathematics_Subtyping2 refines FormalizingMathematics_Subtyping0 {
  
    type S<+X> 
  
    lemma Subtyping(f: S<U> -> bool, y: S<V>)
      ensures f(y) 
  
  }
  // Slide 30 Contravariant subtyping for type parameters

module FormalizingMathematics_Subtyping3 refines FormalizingMathematics_Subtyping0  {
  
    type S<-X> 
  
    lemma Subtyping(f: S<U> -> bool, y: S<T>)
      ensures f(y)
  
  }
  // Slide 31 Restrictions on type synonyms

module FormalizingMathematics_Cardinality {
  
    type S<!X> = X -> bool
  
  }
  // Slide 32 Logic expressiveness

// Slide 33 Theory: integers

module Integers_Theory {
  
    // Constants
    lemma DecimalLiteral() ensures 38 is int
    lemma HexadecimalLiteral() ensures 0xBadDecaf is int
    lemma ReadableLiteral() ensures 4_345_765 is int
    // Functions
    lemma Negation(n: int) ensures -n is int 
    lemma Addition(n: int, m: int) ensures (n + m) is int
    lemma Substraction(n: int, m: int) ensures (n - m) is int
    lemma Multiplication(n: int, m: int) ensures (n * m) is int
    lemma Division(n: int, m: int)
      requires m != 0
      ensures (n / m) is int
    lemma Remainder(n: int, m: int)
      requires m != 0
      ensures (n % m) is int
    // Predicates
    lemma Equality(n: int, m: int) ensures n == m 
    lemma Disequality(n: int, m: int) ensures n != m
    lemma LessOrEqual(n: int, m: int) ensures n <= m
    lemma LessThan(n: int, m: int) ensures n < m
    lemma GreaterOrEqual(n: int, m: int) ensures n >= m
    lemma GreaterThan(n: int, m: int) ensures n > m
  
  }
  // Slide 34 Theory: reals

module Reals_Theory {
  
    // Constants
    lemma DecimalLiteral() ensures 38.98 is real 
    lemma ReadableLiteral() ensures 4_345_765.999_987 is real
    // Functions
    lemma Negation(n: real) ensures -n is real
    lemma Addition(n: real, m: real) ensures (n + m) is real
    lemma Substraction(n: real, m: real) ensures (n - m) is real
    lemma Multiplication(n: real, m: real) ensures (n * m) is real
    lemma Division(n: real, m: real)
      requires m != 0.0
      ensures (n / m) is real
    lemma IntegerToReal(k: int) ensures (k as real) is real
    lemma Floor(n: real) ensures n.Floor is int 
    // Predicates
    lemma Equality(n: real, m: real) ensures n == m
    lemma Disequality(n: real, m: real) ensures n != m
    lemma LessOrEqual(n: real, m: real) ensures n <= m
    lemma LessThan(n: real, m: real) ensures n < m
    lemma GreaterOrEqual(n: real, m: real) ensures n >= m
    lemma GreaterThan(n: real, m: real) ensures n > m
  
  }
  // Slide 35 Theory: finite sets

module Sets_Theory {
  
    // Constants
    lemma EmptySet<T>() ensures {} is set<T> 
  
    // Functions
    lemma Cardinality<T>(A: set<T>) ensures |A| is int 
    lemma Union<T>(A: set<T>, B: set<T>) ensures (A + B) is set<T>
    lemma Intersection<T>(A: set<T>, B: set<T>) ensures (A * B) is set<T>
    lemma AsymmetricDifference<T>(A: set<T>, B: set<T>) ensures (A - B) is set<T>
  
    // Predicates
    lemma Equality<T>(A: set<T>, B: set<T>) ensures A == B
    lemma Disequality<T>(A: set<T>, B: set<T>) ensures A != B
    lemma Subset<T>(A: set<T>, B: set<T>) ensures A <= B
    lemma StrictSubset<T>(A: set<T>, B: set<T>) ensures A < B
    lemma Superset<T>(A: set<T>, B: set<T>) ensures A >= B
    lemma StrictSuperset<T>(A: set<T>, B: set<T>) ensures A > B
    lemma Disjoint<T>(A: set<T>, B: set<T>) ensures A !! B
    lemma Membership<T>(e: T, A: set<T>) ensures e in A
    lemma Absence<T>(e: T, A: set<T>) ensures e !in A
  
  }
  // Slide 36 Theory: sets

module ISets_Theory {
  
    // Functions
    lemma Union<T>(A: iset<T>, B: iset<T>) ensures (A + B) is iset<T>
    lemma Intersection<T>(A: iset<T>, B: iset<T>) ensures (A * B) is iset<T>
    lemma AsymmetricDifference<T>(A: iset<T>, B: iset<T>) ensures (A - B) is iset<T>
  
    // Predicates
    lemma Equality<T>(A: iset<T>, B: iset<T>) ensures A == B
    lemma Disequality<T>(A: iset<T>, B: iset<T>) ensures A != B
    lemma Subset<T>(A: iset<T>, B: iset<T>) ensures A <= B
    lemma StrictSubset<T>(A: iset<T>, B: iset<T>) ensures A < B
    lemma Superset<T>(A: iset<T>, B: iset<T>) ensures A >= B
    lemma StrictSuperset<T>(A: iset<T>, B: iset<T>) ensures A > B
    lemma Disjoint<T>(A: iset<T>, B: iset<T>) ensures A !! B
    lemma In<T>(e: T, A: iset<T>) ensures e in A
    lemma NotIn<T>(e: T, A: iset<T>) ensures e !in A
  
  }
  // Slide 37 Set comprehension

module ISets_Comprehension {
  
    predicate P(x: int)
  
    lemma SetOfPValues() 
      ensures (iset x: int | P(x)) is iset 
  
  }
  