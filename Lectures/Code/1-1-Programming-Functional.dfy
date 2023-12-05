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

// Slide 1 Overview

// Slide 2 Function declaration

module FunctionalProgramming_A1 {

  import opened FunctionalProgramming_Pre

  function FunctionName(x: X, y: Y): R {
    expression
  }

}
// Slide 3 Function body

// Slide 4 Calling a function

module FunctionalProgramming_A1' {

  import opened FunctionalProgramming_Pre

  function F(n: int, m: int): int {
    n + m
  }

  function G(n: int): int {
    F(n + n, n * n)
  }

}
// Slide 5 Constants

module FunctionalProgramming_A1'' {

  import opened FunctionalProgramming_Pre

  const constantName: Type := expression

}
// Slide 6 Predicates

module FunctionalProgramming_A1111 {

  import opened FunctionalProgramming_Pre

  predicate predicateName(x: X, y: Y) {
    booleanExpression
  }

}
// Slide 7 Expressions

// Slide 8 Type test

module FunctionalProgramming_Example {

  predicate IntPlus3IsInt(n: int) { (n + 3) is int }

}
// Slide 9 Booleans

module Booleans_Programming {

  predicate False() { false is bool }

  predicate True() { true is bool }

  predicate Conjunction(a: bool, b: bool) { (a && b) is bool }

  predicate Disjunction(a: bool, b: bool) { (a || b) is bool }

  predicate Implication(a: bool, b: bool) { (a ==> b) is bool }

  predicate Explication(a: bool, b: bool) { (a <== b) is bool }

  predicate Equivalence(a: bool, b: bool) { (a <==> b) is bool }

  predicate Negation(a: bool) { !a is bool }

}
// Slide 10 Integers

module Integers_Programming {

  predicate DecimalLiteral() { 38 is int }
  predicate HexadecimalLiteral() { 0xBadDecaf is int }
  predicate ReadableLiteral() { 4_345_765 is int }
  predicate Negation(n: int) { -n is int }
  predicate Addition(n: int, m: int) { (n + m) is int }
  predicate Substraction(n: int, m: int) { (n - m) is int }
  predicate Multiplication(n: int, m: int) { (n * m) is int }
  predicate {:verify false} Division(n: int, m: int) { (n / m) is int }
  predicate {:verify false} Modulus(n: int, m: int) { (n % m) is int }
  predicate Equality(n: int, m: int) { (n == m) is bool }
  predicate Disequality(n: int, m: int) { (n != m) is bool }
  predicate SmallerOrEqual(n: int, m: int) { (n <= m) is bool }
  predicate Smaller(n: int, m: int) { (n < m) is bool }
  predicate GreaterOrEqual(n: int, m: int) { (n >= m) is bool }
  predicate Greater(n: int, m: int) { (n > m) is bool }

}
// Slide 11 Reals

module Reals_Programming {

  predicate DecimalLiteral() { 38.98 is real }
  predicate ReadableLiteral() { 4_345_765.999_987 is real }
  predicate Negation(n: real) { -n is real }
  predicate Addition(n: real, m: real) { (n + m) is real }
  predicate Substraction(n: real, m: real) { (n - m) is real }
  predicate Multiplication(n: real, m: real) { (n * m) is real }
  predicate {:verify false} Division(n: real, m: real) { (n / m) is real }
  predicate Equality(n: real, m: real) { (n == m) is bool }
  predicate Disequality(n: real, m: real) { (n != m) is bool }
  predicate SmallerOrEqual(n: real, m: real) { (n <= m) is bool }
  predicate Smaller(n: real, m: real) { (n < m) is bool }
  predicate GreaterOrEqual(n: real, m: real) { (n >= m) is bool }
  predicate Greater(n: real, m: real) { (n > m) is bool }
  predicate IntegerToReal(k: int) { (k as real) is real }
  predicate Floor(n: real) { (n.Floor) is int }

}
// Slide 12 Characters

module Characters_Programming {

  predicate ASCII() { 'a' is char }
  predicate SingleQuote() { '\'' is char }
  predicate DoubleQuote() { '\"' is char }
  predicate BackSlash() { '\\' is char }
  predicate NullCharacter() { '\0' is char }
  predicate LineFeed() { '\n' is char }
  predicate CarriageReturn() { '\r' is char }
  predicate Tab() { '\t' is char }
  predicate Unicode() { '\U{1F71D}' is char }
  predicate {:verify false} Addition(a: char, b: char) { (a + b) is char }
  predicate {:verify false} Substraction(a: char, b: char) { (a - b) is char }
  predicate Less(a: char, b: char) { (a < b) is bool }
  predicate LessEqual(a: char, b: char) { (a <= b) is bool }
  predicate Greater(a: char, b: char) { (a > b) is bool }
  predicate GreaterEqual(a: char, b: char) { (a >= b) is bool }

}
// Slide 13 Other expressions

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
// Slide 14 Functions are first-class citizens

// Slide 15 Functions as in-parameters

module FunctionalProgramming_A4 {

  function Apply(f: int -> int, n: int): int {
    f(n)
  }

}
// Slide 16 Functions as out-parameters

module FunctionalProgramming_A5 {

  function ApplyPartial(f: int -> int -> int, n: int): int -> int {
    f(n)
  }

}
// Slide 17 Recursive functions

module FunctionalProgramming_A3 {

  import opened FunctionalProgramming_Pre

  function {:verify false} Factorial(n: int): int {
    if n == 0 then 1 else n * Factorial(n - 1)
  }

}
// Slide 18 New expression: anonymous functions and application

module Expressions_FunctionExpressions {

  predicate LambdaAbstraction<U, V>(expr: V) { ((x: U) => expr) is U -> V }

  predicate Application<U, V>(fun: U -> V, arg: U) { fun(arg) is V }

}
// Slide 19 Algebraic datatypes

module Datatypes_A1 {

  datatype Size =
    | Small
    | Large

}
// Slide 20 Type and constructors

module Datatypes_A2 {

  import opened Datatypes_A1

  predicate Constructor() { Small is Size }

}
// Slide 21 Equality

module Datatypes_A1' {

  import opened Datatypes_A1

  predicate Equality(a: Size, b: Size) { (a == b) is bool }

  predicate Disequality(a: Size, b: Size) { (a != b) is bool }

}
// Slide 22 Pattern matching

module Datatypes_A3 {

  import opened Datatypes_A1

  function SizeToOunces(s: Size): int {
    match s
    case Small => 4
    case Large => 8
  }

}
// Slide 23 New expression: pattern matching

module Datatypes_A4 {

  import opened Datatypes_A1

  predicate MatchExpression(s: Size) {
    (match s case Small => 4 case Large => 8) is int
  }

}
// Slide 24 Parameterized constructors

module Datatypes_A5 {

  import opened Datatypes_A1

  datatype Drink =
    | Coffee(Size)
    | Tea(Size)
    | Water(Size)

}
// Slide 25 Applying constructors

module Datatypes_A6 {

  import opened Datatypes_A1
  import opened Datatypes_A5

  predicate Constructor() { (Tea(Small)) is Drink }

}
// Slide 26 Matching constructors with parameters

module Datatypes_A7 {

  import opened Datatypes_A1
  import opened Datatypes_A3
  import opened Datatypes_A5

  function GetCaffeine(d: Drink): int {
    match d
    case Coffee(s) => 5 * SizeToOunces(s)
    case Tea(s) => 7 * SizeToOunces(s)
    case Water(s) => 0
  }

}
// Slide 27 Wild identifiers on arguments

module Datatypes_A8 {

  import opened Datatypes_A1
  import opened Datatypes_A3
  import opened Datatypes_A5

  function GetCaffeine(d: Drink): int {
    match d
    case Coffee(s) => 5 * SizeToOunces(s)
    case Tea(s) => 7 * SizeToOunces(s)
    case Water(_) => 0
  }

}
// Slide 28 Wild identifiers on constructors

module Datatypes_A9 {

  import opened Datatypes_A1
  import opened Datatypes_A3
  import opened Datatypes_A5

  function GetCaffeine(d: Drink): int {
    match d
    case Coffee(s) => 5 * SizeToOunces(s)
    case Tea(s) => 7 * SizeToOunces(s)
    case _ => 0
  }

}
// Slide 29 Named parameters

module Datatypes_A10 {

  import opened Datatypes_A1

  datatype Drink =
    | Coffee(sz: Size)
    | Tea(sz: Size)
    | Water(sz: Size)

}
// Slide 30 Discriminators and destructors

module Datatypes_A11 {

  import opened Datatypes_A1
  import opened Datatypes_A10

  predicate Discriminator(d: Drink) { d.Coffee? is bool }

  predicate Destructor(d: Drink) { d.sz is Size }

}
// Slide 31 Example with discriminators and destructors

module Datatypes_A12 {

  import opened Datatypes_A1
  import opened Datatypes_A3
  import opened Datatypes_A10

  function GetCaffeine(d: Drink): int {
    if d.Coffee? then
      5 * SizeToOunces(d.sz)
    else if d.Tea? then
      7 * SizeToOunces(d.sz)
    else
      0
  }

}
// Slide 32 Member declarations

module Datatypes_A13_pre {

  datatype Size =
    | Small
    | Large
  {

    predicate This() { this is Size }

  }

}
// Slide 33 Example with member function

module Datatypes_A13 {

  datatype Size =
    | Small
    | Large
  {

    function ToOunces(): int {
      match this
      case Small => 4
      case Large => 8
    }

  }

}
// Slide 34 Functional dot notation

module Datatypes_A14 {

  import opened Datatypes_A13

  predicate DotExpression(s: Size) { s.ToOunces is () -> int }

}
// Slide 35 Records

module Datatypes_A15 {

  datatype Complex = Complex(r: real, i: real)

}
// Slide 36 Type operators

module Polymorphism_A16 {

  datatype List<T> =
    | Nil
    | Cons(head: T, tail: List)

}
// Slide 37 Polymorphism

module Polymorphism_A17 {

  import opened Polymorphism_A16

  function Len<T>(l: List<T>): nat {
    match l
    case Nil => 0
    case Cons(_, tail) => 1 + Len(tail)
  }

}
// Slide 38 Type parameter inference

module Polymorphism_A17' {

  import opened Polymorphism_A16

  function Len<T>(l: List): nat {
    match l
    case Nil => 0
    case Cons(_, tail) => 1 + Len(tail)
  }

}
// Slide 39 Type characteristics

module Polymorphism_A19 {

  function TestEquality<T(==)>(a: T, b: T): bool {
    a == b
  }

}
// Slide 40 Collections

// Slide 41 Sequences

module Sequences_Programming {

  predicate Empty<T>() { [] is seq<T> }
  predicate SequenceDisplay<T>(x: T, y: T, z: T) { [x, y, z] is seq<T> }
  predicate Equality<T(==)>(a: seq, b: seq) { (a == b) is bool }
  predicate Disequality<T(==)>(a: seq, b: seq) { (a != b) is bool }
  predicate ProperPrefix<T(==)>(a: seq, b: seq) { (a < b) is bool }
  predicate Prefix<T(==)>(a: seq, b: seq) { (a <= b) is bool }
  predicate Concatenation<T>(a: seq, b: seq) { (a + b) is seq<T> }
  predicate Membership<T(==)>(a: seq, e: T) { (e in a) is bool }
  predicate Absence<T(==)>(a: seq, e: T) { (e !in a) is bool }
  predicate Size<T>(a: seq) { |a| is int }
  predicate {:verify false} Indexing<T>(a: seq, k: int) { a[k] is T }
  predicate {:verify false} Update<T>(a: seq, k: int, e: T) { a[k := e] is seq<T> }
  predicate {:verify false} Slice<T>(a: seq, k: int, l: int) { a[k..l] is seq<T> }
  predicate {:verify false} Drop<T>(a: seq, k: int) { a[k..] is seq<T> }
  predicate {:verify false} Take<T>(a: seq, l: int) { a[..l] is seq<T> }

}
// Slide 42 Strings

module Strings_Programming {

  predicate Type(s: string) { s is seq<char> }

  predicate Display() { "Hello" is string }

}
// Slide 43 Sets

module Sets_Programming {

  predicate EmptySet<T(==)>() { {} is set<T> }
  predicate SetDisplay<T(==)>(x: T, y: T, z: T) { {x, y, z} is set<T> }
  predicate Union<T(==)>(A: set<T>, B: set<T>) { (A + B) is set<T> }
  predicate Intersection<T(==)>(A: set<T>, B: set<T>) { (A * B) is set<T> }
  predicate AsymmetricDifference<T(==)>(A: set<T>, B: set<T>) { (A - B) is set<T> }
  predicate Equality<T(==)>(A: set<T>, B: set<T>) { (A == B) is bool }
  predicate Disequality<T(==)>(A: set<T>, B: set<T>) { (A != B) is bool }
  predicate Subset<T(==)>(A: set<T>, B: set<T>) { (A <= B) is bool }
  predicate StrictSubset<T(==)>(A: set<T>, B: set<T>) { (A < B) is bool }
  predicate Superset<T(==)>(A: set<T>, B: set<T>) { (A >= B) is bool }
  predicate StrictSuperset<T(==)>(A: set<T>, B: set<T>) { (A > B) is bool }
  predicate Disjoint<T(==)>(A: set<T>, B: set<T>) { (A !! B) is bool }
  predicate Membership<T(==)>(e: T, A: set<T>) { (e in A) is bool }
  predicate Absence<T(==)>(e: T, A: set<T>) { (e !in A) is bool }
  predicate Cardinality<T(==)>(A: set<T>) { |A| is int }

}
// Slide 44 Multisets

module Multisets_Programming {

  predicate EmptyMultiset<T(==)>() { multiset{} is multiset<T> }
  predicate MultisetDisplay<T(==)>(x: T, y: T, z: T) { multiset{x, y, z} is multiset<T> }
  predicate Union<T(==)>(A: multiset<T>, B: multiset<T>) { (A + B) is multiset<T> }
  predicate Intersection<T(==)>(A: multiset<T>, B: multiset<T>) { (A * B) is multiset<T> }
  predicate Difference<T(==)>(A: multiset<T>, B: multiset<T>) { (A - B) is multiset<T> }
  predicate Equality<T(==)>(A: multiset<T>, B: multiset<T>) { (A == B) is bool }
  predicate Disequality<T(==)>(A: multiset<T>, B: multiset<T>) { (A != B) is bool }
  predicate Submultiset<T(==)>(A: multiset<T>, B: multiset<T>) { (A <= B) is bool }
  predicate StrictSubmultiset<T(==)>(A: multiset<T>, B: multiset<T>) { (A < B) is bool }
  predicate Supermultiset<T(==)>(A: multiset<T>, B: multiset<T>) { (A >= B) is bool }
  predicate StrictSupermultiset<T(==)>(A: multiset<T>, B: multiset<T>) { (A > B) is bool }
  predicate Disjoint<T(==)>(A: multiset<T>, B: multiset<T>) { (A !! B) is bool }
  predicate Membership<T(==)>(e: T, A: multiset<T>) { (e in A) is bool }
  predicate Absence<T(==)>(e: T, A: multiset<T>) { (e !in A) is bool }
  predicate Cardinality<T(==)>(A: multiset<T>) { |A| is int }
  predicate Multiplicity<T(==)>(e: T, A: multiset<T>) { A[e] is int }
  predicate {:verify false} MultiplicityUpdate<T(==)>(e: T, A: multiset<T>, k: int) { A[e := k] is multiset<T> }

}
// Slide 45 Maps

module Maps_Programming {

  predicate Empty<U(==), V>() { map[] is map<U, V> }
  predicate Display() { map[20 := true, 3 := false, 20 := false] is map<int,bool>}
  predicate KeyMembership<U(==), V>(m: map, k: U) { (k in m) is bool }
  predicate KeyAbsence<U(==), V>(m: map, k: U) { (k !in m) is bool }
  predicate Cardinality<U(==), V>(m: map) { |m| is int }
  predicate {:verify false} Indexing<U(==), V>(m: map, k: U) { m[k] is V}
  predicate Update<U(==), V>(m: map, k: U, v: V) { m[k := v] is map}
  predicate Keys<U(==), V>(m: map) { m.Keys is set<U> }
  predicate Values<U(==), V(==)>(m: map) { m.Values is set<V> }
  predicate Items<U(==), V(==)>(m: map) { m.Items is set<(U, V)> }
  predicate Merge<U(==), V>(m1: map, m2: map) { (m1 + m2) is map }
  predicate MapDomainSubtraction<U(==), V>(m: map, s: set) { (m - s) is map }

}
// Slide 46 Type synonyms

module FunctionalProgramming_Ainfinite {

  type Complex = (real, real)

}
