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

// Slide 1 Class definition

module ObjectOrientedProgramming_A0 {

  class ClassName {}

  predicate IsObject(c: ClassName) { c is object }

  predicate IsRef(c: ClassName?) { c is object? }

}
// Slide 2 Generic class definition

module ObjectOrientedProgramming_A0' {

  class ClassName<T> {}

}
// Slide 3 Mutable fields

module ObjectOrientedProgramming_A1 {

  class C<T(0)> {

    var mutableField: T

  }

}
// Slide 4 New functional expressions

module ObjectOrientedProgramming_A1' refines ObjectOrientedProgramming_A1 {

  predicate {:verify false} MemberAccess<T(0)>(c: C) { c.mutableField is T }

}
// Slide 5 New RHS expressions

module ObjectOrientedProgramming_A1'' refines ObjectOrientedProgramming_A1 {

  method Allocate<T(0)>() returns (c: C) {
    c := new C;
  }

}
// Slide 6 New $\ell$-values

module ObjectOrientedProgramming_A1''' refines ObjectOrientedProgramming_A1 {

  method {:verify false} Update<T(0)>(c: C, value: T) {
    c.mutableField := value;
  }

}
// Slide 7 Immutable fields

module ObjectOrientedProgramming_A2 {

  class C {

    const immutableField: int := 4

  }

}
// Slide 8 New functional expression: this

module ObjectOrientedProgramming_A5 {

  class C {

    var mutableField: int

    predicate This() { this is C }

  }

}
// Slide 9 Constructors

module ObjectOrientedProgramming_A3 {

  class C {

    var mutableField: int
    const immutableField: int

    constructor (i: int, j: int) {
      immutableField := i;
      mutableField := j;
    }

  }

  method M() {
    var c := new C(3, 4);
  }

}
// Slide 10 Multiple constructors

module ObjectOrientedProgramming_A3' {

  class C {

    var mutableField: int
    const immutableField: int

    constructor Partial(i: int) {
      immutableField := i;
    }

    constructor FromStringLength(s: string) {
      mutableField := 0;
      immutableField := |s|;
    }

    method M() {
      var c := new C.FromStringLength("abc");
    }

  }

}
// Slide 11 Two-phase construction

module ObjectOrientedProgramming_A4 {

  class C {

    var mutableField: int
    const immutableField: int

    constructor(i: int, j: int) {
      immutableField := i;
      new;
      mutableField := j;
    }

  }

}
// Slide 12 Other member declarations/definitions

module ObjectOrientedProgramming_A6 {

  class C {

    var mutableField: int

    method Print() {
      print mutableField, "\n";
    }

    function {:verify false} Get(): int {
      mutableField
    }

  }

}
// Slide 13 Traits

module ObjectOrientedProgramming_B1 {

  trait TraitName { }

}
// Slide 14 Inheritance

module ObjectOrientedProgramming_Inheritance {

  trait T {
    method Print() { print("Hello, World!"); }
  }

  class C extends T {
    method RePrint() { Print(); }
  }

}
// Slide 15 Subtyping

module ObjectOrientedProgramming_Subtyping {

  trait A {
    method Print() { print("Hello, World!"); }
  }

  trait B extends A {}
  
  method M1(o: A) { o.Print(); }
  
  method M2(o: B) { M1(o); }

}
// Slide 16 Late binding

module ObjectOrientedProgramming_LateBinding {

  trait T {

    function G(x: int): int
    
    function F(x: int): int { G(x) }

  }

  class C extends T {
    
    function G(x: int): int { x + 1 }
  
  }

}
// Slide 17 Overriding

// Slide 18 Encapsulation

module ObjectOrientedProgramming_Encapsulation {

  trait Complex {
    function Real(): real
    function Im(): real
  }

  class PolarComplex extends Complex {
  
    var r: real
    var i: real
  
    function {:verify false} Real(): real { r }
    function {:verify false} Im(): real { r }
  
  }

}
// Slide 19 Dynamic dispatch

module ObjectOrientedProgramming_DynamicDispatch {

  trait Printer {
    method Print()
  }
  class A extends Printer {
    method Print() { print("A\n"); }
  }
  class B extends Printer {
    method Print() { print("B\n"); }
  }

  method Print(p: Printer) {
    p.Print();
  }

  method Main() {

    var a := new A;
    var b := new B;
    Print(a);
    Print(b);

  }

}
// Slide 20 Conclusion

