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

module ImperativeProgramming_M1 {

  method MethodName<T>(x: T, y: string) {
    print x;
    print y;
  }

}
// Slide 2 Statement: method call

module ImperativeProgramming_M1' refines ImperativeProgramming_M1 {

  method Call() {

    MethodName("Hello, ", "World\n");

  }

}
// Slide 3 Statement: variable declaration

module ImperativeProgramming_M3 {

  import opened ImperativeProgramming_M2Pre

  method VariableDeclaration() {

    var x: int := integerExpression;

  }

}
// Slide 4 Statement: assignment

module ImperativeProgramming_M4 {

  import opened ImperativeProgramming_M2Pre

  method Assignment() {

    var x := integerExpression;
    x := x + 1;

  }

}
// Slide 5 Example variable declarations and assignments

module ImperativeProgramming_VarDeclExamples {

  import opened ImperativeProgramming_M2Pre

  method Assignment() {

    var w: int := integerExpression;

    var x: int;
    x := integerExpression;

    var y := integerExpression;

    var z;
    z := integerExpression;

  }

}
// Slide 6 Method out-parameters

module ImperativeProgramming_MParameters {

  method MultipleInsAndOuts(a: int, b: int) returns (x: int, y: int) {

    x := a + b;
    y := x + 1;

  }

}
// Slide 7 Statement: return

module ImperativeProgramming_Return {

  method MultipleInsAndOuts(a: int, b: int) returns (x: int, y: int) {

    x := a + b;
    y := x + 1;
    return;
    y := 500; // this statement is never reached

  }

}
// Slide 8 Statement: return with arguments

module ImperativeProgramming_M2 {

  import opened ImperativeProgramming_M2Pre

  method Return() returns (o: int) {

    return integerExpression;

  }

  method ReturnArgumentsMeaning() returns (o: int) {

    o := integerExpression;
    return;

  }

}
// Slide 9 Statement: method call with out-parameter

module ImperativeProgramming_M1'' {

  import opened ImperativeProgramming_M2
  import opened ImperativeProgramming_MParameters

  method Calls() {

    var s: int := Return();
    var x, y := MultipleInsAndOuts(20, 30);

  }

}
// Slide 10 Statement: conditional

module ImperativeProgramming_M6 {

  import opened ImperativeProgramming_PreFlow

  method If() {

    if booleanExpression {
      // ...
    }

  }

}
// Slide 11 Statement: alternative conditional

module ImperativeProgramming_M7 {

  import opened ImperativeProgramming_PreFlow

  method IfElse() {

    if booleanExpression {
      // ...
    } else {
      // ...
    }

  }

}
// Slide 12 Statement: cascading if

module ImperativeProgramming_M7' {

  import opened ImperativeProgramming_PreFlow

  method CascadingIf() {

    if booleanExpressionA {
      // ...
    } else if booleanExpressionB {
      // ...
    } else {
      // ...
    }

  }

}
// Slide 13 Statement: while loops

module ImperativeProgramming_M8 {

  import opened ImperativeProgramming_PreFlow

  method {:verify false} WhileLoop() {

    while booleanExpression {
      // ...
    }

  }

}
// Slide 14 Statement: for loops

module ImperativeProgramming_M9 {

  import opened ImperativeProgramming_PreFlow

  method ForLoop() {

    for x := loExpression to hiExpression {
      // ...
    }

    for x := hiExpression downto loExpression {
      // ...
    }

  }

}
// Slide 15 Statement: match

module ImperativeProgramming_M10 {

  import opened ImperativeProgramming_PreMatch

  method Match() {

    match datatypeValue {
      case Case1 => // ...
      case Case2 => // ...
    }

  }

}
// Slide 16 Failure-compatible types

module ImperativeProgramming_M11 {

  datatype Status<T> =
    | Success(value: T)
    | Failure(error: string)
  {

    predicate IsFailure() { this.Failure? }

    function PropagateFailure(): Status<T> { this }

    function {:verify false} Extract(): T { this.value }

  }

}
// Slide 17 Statement: failure-propagating assignment

module ImperativeProgramming_M12 refines ImperativeProgramming_M11 {

  method Callee(i: int) returns (r: Status<int>)
  {
    if i < 0 {
      return Failure("negative");
    }
    return Success(i);
  }

  method Caller(i: int) returns (r: Status<int>)
  {
    var x: int :- Callee(i);
    return Success(x + 5);
  }

  method CallerMeaning(i: int) returns (r: Status<int>)
  {
    var tmp: Status<int> := Callee(i);
    if tmp.IsFailure() {
      return tmp.PropagateFailure();
    }
    var x: int := tmp.Extract();

    return Success(x + 5);
  }

}
// Slide 18 Arrays

// Slide 19 Array rhs expression: creation

module Arrays_A2 {

  method {:verify false} Allocate<T>(size: int) returns (arr: array<T>) {
    arr := new T[size];
  }

}
// Slide 20 References

module Arrays_A4 {

  method Aliasing() {

    var arr := new int[100];
    var brr := arr;

  }

}
// Slide 21 Allocatedness

module Arrays_A5 {

  predicate Null<T>() { null is array?<T> }

  predicate IsNull<T>(arr: array?) { (arr == null) is bool }

}
// Slide 22 Array functional expressions

module Arrays_A1 {

  predicate {:verify false} Indexing<T>(arr: array<T>, index: int) { arr[index] is T }

  predicate Length<T>(arr: array<T>) { arr.Length is int }
  
  predicate {:verify false} ToSequence<T>(arr: array<T>) { arr[..] is seq<T> }

}
// Slide 23 Array $\ell$-value: update

module Arrays_A3 {

  method {:verify false} Update<T>(arr: array<T>, index: int, value: T) {
    arr[index] := value;
  }

}
