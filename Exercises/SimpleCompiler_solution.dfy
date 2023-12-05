
// In this exercise, you will prove the correctness of a compiler. We need a few definitions to formalize the operational semantics of our source and target language. First, we define 0 or more transitions.
least predicate star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
  (conf1 == conf2) || (exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

// Exercise
// Prove
lemma star_one_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
  requires R(conf1,conf2)
  ensures star(R,conf1,conf2)
{
}

// Exercise
// Prove
lemma star_one<T(!new)>()
  ensures forall R: (T,T) -> bool :: forall conf1, conf2: T :: R(conf1,conf2) ==> star(R,conf1,conf2)
{
}

// Exercise
// Prove
least lemma star_trans_pre<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
  requires star(R,conf1,conf2)
  ensures  star(R,conf2,conf3) ==> star(R,conf1,conf3)
{
  if conf1 == conf2 {}
  else {
    var confi :| R(conf1, confi) && star(R,confi, conf2);
    assert star(R,confi,conf2);
    star_trans_pre(R,confi,conf2,conf3);
  }
}

// Exercise
// Prove
lemma star_trans_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
  requires star(R,conf1,conf2)
  requires star(R,conf2,conf3)
  ensures star(R,conf1,conf3)
{
  star_trans_pre(R,conf1,conf2,conf3);
}

// Exercise
// Prove
lemma star_trans<T(!new)>()
  ensures forall R: (T,T) -> bool :: forall conf1, conf2, conf3: T :: (star(R,conf1,conf2) && star(R,conf2,conf3)) ==> star(R,conf1,conf3)
{
  forall R, conf1, conf2, conf3: T ensures (star(R,conf1,conf2) && star(R,conf2,conf3)) ==> star(R,conf1,conf3) {
    if star(R,conf1,conf2) {
      star_trans_pre(R,conf1,conf2,conf3);
    }
  }
}

// A transition that makes at least one step.
least predicate plus<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
  (exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

// Exercise
// Prove
lemma plus_one<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
  requires R(conf1,conf2)
  ensures star(R,conf1,conf2)
{
}

// Exercise
// Prove
lemma plus_star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
  requires plus(R,conf1,conf2)
  ensures star(R,conf1,conf2)
{
  var conf1' :| R(conf1, conf1') && star(R,conf1', conf2);
  star_one_sequent(R,conf1,conf1');
  star_trans_sequent(R,conf1,conf1',conf2);
}

// Exercise
// Prove
lemma star_plus_trans<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
  requires star(R,conf1,conf2)
  requires plus(R,conf2,conf3)
  ensures plus(R,conf1,conf3)
{
  if conf1 == conf2 {
  } else {
    var conf1' :| R(conf1, conf1') && star(R,conf1', conf2);
    var conf2' :| R(conf2, conf2') && star(R,conf2', conf3);
    star_one_sequent(R,conf2,conf2');
    star_trans_sequent(R,conf1',conf2,conf2');
    star_trans_sequent(R,conf1',conf2',conf3);
  }
}

// Identifier.
type ident = string

// Definition of arithmetic expressions.
datatype aexp =
  | CONST(n: int)
  | VAR(x: ident)
  | PLUS(a1: aexp, a2: aexp)
  | MINUS(a1: aexp, a2: aexp)

// Predicate that test whether some identifier appears in arithmetic expression.
predicate id_in_aexp(id: ident, a: aexp) {
  match a
  case CONST(n) => false
  case VAR(id') => id == id'
  case PLUS(a1, a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
  case MINUS(a1, a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
}

// The program store is modeled as a map from identifiers to integers
type store = map<ident,int>

// Define a function that evaluates an arithmetic expression.
function aeval(s: store, a: aexp): int
  requires forall id: ident :: id_in_aexp(id,a) ==> id in s
{
  match a
  case CONST(n) => n
  case VAR(id) => s[id]
  case PLUS(a1, a2) => aeval(s,a1) + aeval(s,a2)
  case MINUS(a1, a2) => aeval(s,a1) - aeval(s,a2)
}

// Definition of Boolean expressions.
datatype bexp =
  | TRUE
  | FALSE
  | EQUAL(a1: aexp, a2: aexp)
  | LESSEQUAL(a1: aexp, a2: aexp)
  | NOT(b1: bexp)
  | AND(b1: bexp, b2: bexp)

// Predicate that test whether some identifier appears in arithmetic expression.
predicate id_in_bexp(id: ident, b: bexp) {
  match b
  case TRUE => true
  case FALSE => false
  case EQUAL(a1,a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
  case LESSEQUAL(a1,a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
  case NOT(b) => id_in_bexp(id,b)
  case AND(b1,b2) => id_in_bexp(id,b1) || id_in_bexp(id,b2)
}

// Define a function that evaluates a Boolean expression.
function beval(s: store, b: bexp): bool
  requires forall id: ident :: id_in_bexp(id,b) ==> id in s
{
  match b
  case TRUE => true
  case FALSE => false
  case EQUAL(a1, a2) => aeval(s,a1) == aeval(s,a2)
  case LESSEQUAL(a1, a2) => aeval(s,a1) <= aeval(s,a2)
  case NOT(b) => ! beval(s,b)
  case AND(b1,b2) => beval(s,b1) && beval(s,b2)
}

// Definition of commands, or statements.
datatype com =
  | SKIP
  | ASSIGN(x: ident, a: aexp)
  | SEQ(c1: com, c2: com)
  | IFTHENELSE(b: bexp, c1: com, c2: com)
  | WHILE(b: bexp, c1: com)

// Predicate that test whether some identifier appears in arithmetic expression.
predicate id_in_com(id: ident, c: com) {
  match c
  case SKIP => false
  case ASSIGN(id',a) => id_in_aexp(id,a)
  case SEQ(c1, c2) => id_in_com(id,c1) || id_in_com(id,c2)
  case IFTHENELSE(b,c1,c2) => id_in_bexp(id,b) || id_in_com(id,c1) || id_in_com(id,c2)
  case WHILE(b,c) => id_in_bexp(id,b) || id_in_com(id,c)
}

// Exercise
// Define the semantics of commands using a least fixed-point.
least predicate cexec(s1: store, c: com, s2: store)
{
  match c
  case SKIP => s1 == s2
  case ASSIGN(id,a) =>
    if (forall id: ident :: id_in_aexp(id,a) ==> id in s1) then s2 == s1[id := aeval(s1,a)] else false
  case SEQ(c1, c2) => exists si: store :: cexec(s1,c1,si) && cexec(si,c2,s2)
  case IFTHENELSE(b,c1,c2) =>
    if (forall id: ident :: id_in_bexp(id,b) ==> id in s1) then
      (if beval(s1,b) then cexec(s1,c1,s2) else cexec(s1,c2,s2))
    else false
  case WHILE(b,c) =>
    if (forall id: ident :: id_in_bexp(id,b) ==> id in s1) then
      if beval(s1,b) then (exists si: store :: cexec(s1,c,si) && cexec(si,WHILE(b,c),s2)) else s1 == s2
    else false
}

// An offset in the assembly code.
type offset = int

// Definition of the assembly language.
datatype instr =
  | Iconst(n: int)
  | Ivar(x: ident)
  | Isetvar(x: string)
  | Iadd
  | Iopp
  | Ibranch(d: offset)
  | Ibeq(d1: offset, d0: offset)
  | Ible(d1: offset, d0: offset)
  | Ihalt

// An assembly code is a sequence of instructions and its execution requires a code pointer, a stack of integers, and a store.
type code = seq<instr>

type stack = seq<int>

type config = (nat,stack,store)

// Exercise
// Define the transition of the assembly machine.
predicate transition(c: code, conf1: config, conf2: config) 
{
  var (pc1,stk1,st1) := conf1;
  var (pc2,stk2,st2) := conf2;
  if ! (pc1 < |c|) then false else
  match c[pc1]
  case Iconst(n) =>
    && pc2 == pc1 + 1
    && stk2 == [n] + stk1
    && st1 == st2
  case Ivar(id) =>
    && pc2 == pc1 + 1
    && (id in st1) && (stk2 == [st1[id]] + stk1)
    && st1 == st2
  case Isetvar(id) =>
    && pc2 == pc1 + 1
    && |stk1| > 0 && stk2 == stk1[1..]
    && st2 == st1[id := stk1[0]]
  case Iadd =>
    && pc2 == pc1 + 1
    && |stk1| > 1 && stk2 == [stk1[0] + stk1[1]] + stk1[2..]
    && st1 == st2
  case Iopp =>
    && pc2 == pc1 + 1
    && |stk1| > 0 && stk2 == [-stk1[0]] + stk1[1..]
    && st1 == st2
  case Ibranch(ofs) =>
    && pc2 == pc1 + 1 + ofs
    && stk2 == stk1
    && st1 == st2
  case Ibeq(ofs1,ofs2) =>
    && |stk1| > 1 && pc2 == pc1 + 1 + (if stk1[0] == stk1[1] then ofs1 else ofs2)
    && stk2 == stk1[2..]
    && st1 == st2
  case Ible(ofs1,ofs2) =>
    && |stk1| > 1 && pc2 == pc1 + 1 + (if stk1[1] <= stk1[0] then ofs1 else ofs2)
    && stk2 == stk1[2..]
    && st1 == st2
  case Ihalt => false
}

// Exercise
// Define a sequence of transitions.
ghost predicate transitions(C: code, conf1: config, conf2: config) 
{
  star((c1,c2) => transition(C,c1,c2),conf1,conf2)
}

// Exercise
// Define termination for an assembly execution.
ghost predicate machine_terminates(C: code, s_init: store, s_final: store) 
{
  exists pc: nat :: transitions(C,(0,[],s_init),(pc,[],s_final)) && pc < |C| && C[pc] == Ihalt
}

// Exercise
// Define a function that compiles an arithmetic expression to assembly code.
function compile_aexp(a: aexp): code 
{
  match a {
    case CONST(n) => [Iconst(n)]
    case VAR(id) => [Ivar(id)]
    case PLUS(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Iadd]
    case MINUS(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Iopp,Iadd]
  }
}

// Exercise
// Define a function that compiles a Boolean expression to assembly code.
function compile_bexp(b: bexp, d1: int, d0: int): code 
{
  match b {
    case TRUE => if d1 == 0 then [] else [Ibranch(d1)]
    case FALSE => if d0 == 0 then [] else [Ibranch(d0)]
    case EQUAL(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Ibeq(d1,d0)]
    case LESSEQUAL(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Ible(d1,d0)]
    case NOT(b1) => compile_bexp(b1, d0, d1)
    case AND(b1, b2) =>
      var c2 := compile_bexp(b2, d1, d0);
      var c1 := compile_bexp(b1, 0, |c2| + d0);
      c1 + c2
  }
}

// Exercise
// Define a function that compiles a command to assembly code.
function compile_com(c: com): code 
{
  match c {
    case SKIP => []
    case ASSIGN(id, a) => compile_aexp(a) + [Isetvar(id)]
    case SEQ(c1, c2) => compile_com(c1) + compile_com(c2)
    case IFTHENELSE(b, ifso, ifnot) =>
      var code_ifso := compile_com(ifso);
      var code_ifnot := compile_com(ifnot);
      compile_bexp(b,0,|code_ifso| + 1)
      + code_ifso + [Ibranch(|code_ifnot|)] + code_ifnot
    case WHILE(b, body) =>
      var code_body := compile_com(body);
      var code_test := compile_bexp(b,0,|code_body|+1);
      code_test + code_body + [Ibranch(-( |code_test| + |code_body| + 1))]
  }
}

// Exercise
// Define the compilation of an entire program to assembly code.
function compile_program(p: com): code 
{
  compile_com(p) + [Ihalt]
}

// The following predicates allows us to structure the assemble code, it will be very handy.
ghost predicate code_at(C: code, pc: nat, C2: code) {
  exists C1, C3: code :: C == C1 + C2 + C3 && |C1| == pc
}

// Exercise
// Prove.
lemma code_at_app_left(C: code, pc: nat, C1: code, C2: code)
  requires code_at(C,pc,C1 + C2)
  ensures code_at(C,pc,C1)
{
  var C0, C3 :| C == C0 + (C1 + C2) + C3 && |C0| == pc;
  assert C == C0 + C1 + (C2 + C3) && |C0| == pc;
}

// Exercise
// Prove.
lemma code_at_app_right(C: code, pc: nat, C1: code, C2: code)
  requires code_at(C,pc,C1 + C2)
  ensures code_at(C,pc + |C1|,C2)
{
  var C0, C3 :| C == C0 + (C1 + C2) + C3 && |C0| == pc;
  assert C == (C0 + C1) + C2 + C3 && |C0 + C1| == pc + |C1|;
}

// Exercise
// Prove.
lemma resolve_code_at()
  ensures forall C: code :: forall pc: nat :: forall C1, C2: code :: code_at(C,pc,C1 + C2) ==> code_at(C,pc,C1)
  ensures forall C: code :: forall pc: nat :: forall C1, C2: code :: code_at(C,pc,C1 + C2) ==> code_at(C,pc + |C1|,C2)
{
  forall C, pc, C1, C2 ensures code_at(C,pc,C1 + C2) ==> code_at(C,pc,C1) {
    if code_at(C,pc,C1 + C2) {
      code_at_app_left(C,pc,C1,C2);
    }
  }
  // Surprisingly, in what follows, if we do not provide the type annotation on pc,
  // then Dafny fails to recognize that pc is a nat
  forall C, pc: nat, C1, C2 ensures code_at(C,pc,C1 + C2) ==> code_at(C,pc + |C1|,C2) {
    if code_at(C,pc,C1 + C2) {
      code_at_app_right(C,pc,C1,C2);
    }
  }
}

// Exercise
// Prove that the compilation of arithmetic expressions is correct.
lemma compile_aexp_correct(C: code, s: store, a: aexp, pc: nat, stk: stack)
  requires forall id: ident :: id_in_aexp(id,a) ==> id in s
  requires code_at(C,pc,compile_aexp(a))
  ensures transitions(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s))
{
  var conf1 := (pc,stk,s);
  var conf2 := (pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s);
  var tr := (c1,c2) => transition(C,c1,c2);
  match a {

    case CONST(n) => {

      assert aeval(s,a) == n;
      assert compile_aexp(a) == [Iconst(n)];
      assert |compile_aexp(a)| == 1;
      assert C[pc] == Iconst(n);
      assert transition(C,(pc,stk,s),(pc + 1, [n] + stk,s));
      assert transition(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk,s));
      star_one_sequent<config>(tr,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk,s));

    }

    case VAR(id) => star_one_sequent<config>(tr,conf1,conf2);

    case PLUS(a1, a2) => {
      assert code_at(C,pc,compile_aexp(a1)) by { resolve_code_at(); }
      compile_aexp_correct(C,s,a1,pc,stk);
      assert code_at(C,pc + |compile_aexp(a1)|,compile_aexp(a2)) by { resolve_code_at(); }
      compile_aexp_correct(C,s,a2,pc + |compile_aexp(a1)|,[aeval(s,a1)] + stk);
      var confi1 := (pc + |compile_aexp(a1)|,[aeval(s,a1)] + stk,s);
      assert star<config>(tr,conf1,confi1);
      var confi2 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|,[aeval(s,a2)] + ([aeval(s,a1)] + stk),s);
      assert star<config>(tr,confi1,confi2);
      star_trans_sequent<config>(tr,conf1,confi1,confi2);
      star_one_sequent<config>(tr,confi2,conf2);
      star_trans_sequent<config>(tr,conf1,confi2,conf2);
    }

    case MINUS(a1, a2) => {
      assert code_at(C,pc,compile_aexp(a1)) by { resolve_code_at(); }
      compile_aexp_correct(C,s,a1,pc,stk);
      assert code_at(C,pc + |compile_aexp(a1)|,compile_aexp(a2)) by { resolve_code_at(); }
      compile_aexp_correct(C,s,a2,pc + |compile_aexp(a1)|,[aeval(s,a1)] + stk);
      var confi1 := (pc + |compile_aexp(a1)|,[aeval(s,a1)] + stk,s);
      assert star<config>(tr,conf1,confi1);
      var confi2 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|,[aeval(s,a2)] + ([aeval(s,a1)] + stk),s);
      assert star<config>(tr,confi1,confi2);
      star_trans_sequent<config>(tr,conf1,confi1,confi2);
      var confi3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)| + 1,[-aeval(s,a2)] + ([aeval(s,a1)] + stk),s);
      star_one_sequent<config>(tr,confi2,confi3);
      star_one_sequent<config>(tr,confi3,conf2);
      star_trans_sequent<config>(tr,conf1,confi2,conf2);

    }
  }
}

// Exercise
// Generalized version of the theorem for more automation.
lemma compile_aexp_correct_gen()
  ensures forall C: code :: forall s: store :: forall a: aexp :: forall pc: nat :: forall stk: stack :: (forall id: ident :: id_in_aexp(id,a) ==> id in s) ==> code_at(C,pc,compile_aexp(a)) ==> transitions(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s)) {
  forall C, s, a, pc: nat, stk ensures (forall id: ident :: id_in_aexp(id,a) ==> id in s) ==> code_at(C,pc,compile_aexp(a)) ==> transitions(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s)) {
    if (forall id: ident :: id_in_aexp(id,a) ==> id in s) {
      if code_at(C,pc,compile_aexp(a)) {
        compile_aexp_correct(C, s, a, pc, stk);
      }
    }
  }
}

// Exercise
// Prove that the compilation of Boolean expressions is correct. We will do this as two separate but mutually recursive lemmas, which is easy to do in Dafny.
lemma compile_bexp_correct_true(C: code, s: store, b: bexp, pc: nat, d1: nat, d0: nat, stk: stack)
  requires forall id: ident :: id_in_bexp(id,b) ==> id in s
  requires code_at(C,pc,compile_bexp(b,d1,d0))
  requires beval(s,b)
  ensures transitions(C,(pc,stk,s),(pc + |compile_bexp(b,d1,d0)| + d1, stk, s))
{
  var tr := (c1,c2) => transition(C,c1,c2);

  match b {

    case TRUE => {
      assert {:split_here} true;
      if d1 == 0 {
      } else {
        var conf1 := (pc,stk,s);
        var conf2 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
        assert beval(s,b);
        assert C[pc] == Ibranch(d1);
        assert transition(C,conf1,conf2);
        star_one_sequent<config>(tr,conf1,conf2);
      }
    }

    case FALSE => assert !beval(s,b);

    case EQUAL(a1, a2) => {
      assert {:split_here} true;

      var conf1 := (pc,stk,s);
      var conf2 := (pc + |compile_aexp(a1)|, [aeval(s,a1)] + stk, s);
      assert transitions(C,conf1,conf2) by { resolve_code_at(); compile_aexp_correct_gen(); }
      assert star<config>(tr,conf1,conf2);

      var conf3i := ((pc + |compile_aexp(a1)|) + |compile_aexp(a2)|, [aeval(s,a2)] + ([aeval(s,a1)] + stk), s);
      assert transitions(C,conf2,conf3i) by { resolve_code_at(); compile_aexp_correct_gen(); }

      var conf3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|, [aeval(s,a2)] + [aeval(s,a1)] + stk, s);
      assert transitions(C,conf2,conf3) by {
        assert (pc + |compile_aexp(a1)|) + |compile_aexp(a2)| == pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
        assert [aeval(s,a2)] + ([aeval(s,a1)] + stk) == [aeval(s,a2)] + [aeval(s,a1)] + stk;
      }
      assert star<config>(tr,conf2,conf3);

      var stk' := [aeval(s,a2)] + [aeval(s,a1)] + stk;
      assert C[pc + |compile_aexp(a1)| + |compile_aexp(a2)|] == Ibeq(d1,d0);
      assert stk == stk'[2..];
      assert |stk'| > 1;
      var pcs := pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
      assert pc + |compile_bexp(b,d1,d0)| + d1 == pcs + 1 + (if stk'[0] == stk'[1] then d1 else d0);

      var conf4 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
      assert transition(C,conf3,conf4);

      star_one_sequent<config>(tr,conf3,conf4);

      star_trans_sequent<config>(tr,conf1,conf2,conf3);
      star_trans_sequent<config>(tr,conf1,conf3,conf4);

    }

    case LESSEQUAL(a1, a2) => {
      assert {:split_here} true;

      var conf1 := (pc,stk,s);
      var conf2 := (pc + |compile_aexp(a1)|, [aeval(s,a1)] + stk, s);
      assert transitions(C,conf1,conf2) by { resolve_code_at(); compile_aexp_correct_gen(); }
      assert star<config>(tr,conf1,conf2);

      var conf3i := ((pc + |compile_aexp(a1)|) + |compile_aexp(a2)|, [aeval(s,a2)] + ([aeval(s,a1)] + stk), s);
      assert transitions(C,conf2,conf3i) by { resolve_code_at(); compile_aexp_correct_gen(); }

      var conf3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|, [aeval(s,a2)] + [aeval(s,a1)] + stk, s);
      assert transitions(C,conf2,conf3) by {
        assert (pc + |compile_aexp(a1)|) + |compile_aexp(a2)| == pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
        assert [aeval(s,a2)] + ([aeval(s,a1)] + stk) == [aeval(s,a2)] + [aeval(s,a1)] + stk;
      }
      assert star<config>(tr,conf2,conf3);

      var stk' := [aeval(s,a2)] + [aeval(s,a1)] + stk;
      assert C[pc + |compile_aexp(a1)| + |compile_aexp(a2)|] == Ible(d1,d0);
      assert stk == stk'[2..];
      assert |stk'| > 1;
      var pcs := pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
      assert pc + |compile_bexp(b,d1,d0)| + d1 == pcs + 1 + (if stk'[1] <= stk'[0] then d1 else d0);

      var conf4 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
      assert transition(C,conf3,conf4);

      star_one_sequent<config>(tr,conf3,conf4);

      star_trans_sequent<config>(tr,conf1,conf2,conf3);
      star_trans_sequent<config>(tr,conf1,conf3,conf4);

    }

    case NOT(b1) => {
      assert {:split_here} true;

      var conf1 := (pc,stk,s);
      assert !beval(s,b1);

      compile_bexp_correct_false(C, s, b1, pc, d0, d1, stk);

    }

    case AND(b1, b2) => {
      assert {:split_here} true;

      var conf1 := (pc,stk,s);
      assert code_at(C,pc,compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)) by { resolve_code_at(); }
      var conf2 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|,stk,s);
      assert transitions(C,conf1,conf2) by {
        compile_bexp_correct_true(C, s, b1, pc, 0, |compile_bexp(b2, d1, d0)| + d0, stk);
      }
      assert star<config>(tr,conf1,conf2);

      assert code_at(C,pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|,compile_bexp(b2, d1, d0)) by { resolve_code_at(); }
      var conf3 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)| + |compile_bexp(b2, d1, d0)| + d1,stk,s);
      assert transitions(C,conf2,conf3) by {
        compile_bexp_correct_true(C, s, b2, pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|, d1, d0, stk);
      }
      assert star<config>(tr,conf2,conf3);
      star_trans_sequent<config>(tr,conf1,conf2,conf3);

    }

  }

}

// Exercise
// Second part of the proof.
lemma compile_bexp_correct_false(C: code, s: store, b: bexp, pc: nat, d1: nat, d0: nat, stk: stack)
  requires forall id: ident :: id_in_bexp(id,b) ==> id in s
  requires code_at(C,pc,compile_bexp(b,d1,d0))
  requires !beval(s,b)
  ensures transitions(C,(pc,stk,s),(pc + (|compile_bexp(b,d1,d0)| + d0), stk, s))
{
  var tr := (c1,c2) => transition(C,c1,c2);

  match b {

    case TRUE => assert beval(s,b);

    case FALSE => {
      assert {:split_here} true;
      if d0 == 0 {
      } else {
        var conf1 := (pc,stk,s);
        var conf2 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
        assert !beval(s,b);
        assert C[pc] == Ibranch(d0);
        assert transition(C,conf1,conf2);
        star_one_sequent<config>(tr,conf1,conf2);
      }
    }

    case EQUAL(a1, a2) => {
      assert {:split_here} true;

      var conf1 := (pc,stk,s);
      var conf2 := (pc + |compile_aexp(a1)|, [aeval(s,a1)] + stk, s);
      assert transitions(C,conf1,conf2) by { resolve_code_at(); compile_aexp_correct_gen(); }
      assert star<config>(tr,conf1,conf2);

      var conf3i := ((pc + |compile_aexp(a1)|) + |compile_aexp(a2)|, [aeval(s,a2)] + ([aeval(s,a1)] + stk), s);
      assert transitions(C,conf2,conf3i) by { resolve_code_at(); compile_aexp_correct_gen(); }

      var conf3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|, [aeval(s,a2)] + [aeval(s,a1)] + stk, s);
      assert transitions(C,conf2,conf3) by {
        assert (pc + |compile_aexp(a1)|) + |compile_aexp(a2)| == pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
        assert [aeval(s,a2)] + ([aeval(s,a1)] + stk) == [aeval(s,a2)] + [aeval(s,a1)] + stk;
      }
      assert star<config>(tr,conf2,conf3);

      var stk' := [aeval(s,a2)] + [aeval(s,a1)] + stk;
      assert C[pc + |compile_aexp(a1)| + |compile_aexp(a2)|] == Ibeq(d1,d0);
      assert stk == stk'[2..];
      assert |stk'| > 1;
      var pcs := pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
      assert pc + |compile_bexp(b,d1,d0)| + d0 == pcs + 1 + (if stk'[0] == stk'[1] then d1 else d0);

      var conf4 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
      assert transition(C,conf3,conf4);

      star_one_sequent<config>(tr,conf3,conf4);

      star_trans_sequent<config>(tr,conf1,conf2,conf3);
      star_trans_sequent<config>(tr,conf1,conf3,conf4);

    }

    case LESSEQUAL(a1, a2) => {
      assert {:split_here} true;

      var conf1 := (pc,stk,s);
      var conf2 := (pc + |compile_aexp(a1)|, [aeval(s,a1)] + stk, s);
      assert transitions(C,conf1,conf2) by { resolve_code_at(); compile_aexp_correct_gen(); }
      assert star<config>(tr,conf1,conf2);

      var conf3i := ((pc + |compile_aexp(a1)|) + |compile_aexp(a2)|, [aeval(s,a2)] + ([aeval(s,a1)] + stk), s);
      assert transitions(C,conf2,conf3i) by { resolve_code_at(); compile_aexp_correct_gen(); }

      var conf3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|, [aeval(s,a2)] + [aeval(s,a1)] + stk, s);
      assert transitions(C,conf2,conf3) by {
        assert (pc + |compile_aexp(a1)|) + |compile_aexp(a2)| == pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
        assert [aeval(s,a2)] + ([aeval(s,a1)] + stk) == [aeval(s,a2)] + [aeval(s,a1)] + stk;
      }
      assert star<config>(tr,conf2,conf3);

      var stk' := [aeval(s,a2)] + [aeval(s,a1)] + stk;
      assert C[pc + |compile_aexp(a1)| + |compile_aexp(a2)|] == Ible(d1,d0);
      assert stk == stk'[2..];
      assert |stk'| > 1;
      var pcs := pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
      assert pc + |compile_bexp(b,d1,d0)| + d0 == pcs + 1 + (if stk'[1] <= stk'[0] then d1 else d0);

      var conf4 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
      assert transition(C,conf3,conf4);

      star_one_sequent<config>(tr,conf3,conf4);

      star_trans_sequent<config>(tr,conf1,conf2,conf3);
      star_trans_sequent<config>(tr,conf1,conf3,conf4);

    }

    case NOT(b1) => {
      assert {:split_here} true;

      var conf1 := (pc,stk,s);
      assert beval(s,b1);

      compile_bexp_correct_true(C, s, b1, pc, d0, d1, stk);

    }

    case AND(b1, b2) => {
      assert {:split_here} true;

      // This case if more interesting because and is compiled as a lazy and.
      // So, if it is false, two things could have happened
      // If eval(s,b1) was false, we branched directly without executing b2
      // Otherwise, eval(s,b2) was false

      if beval(s,b1) {

        assert !beval(s,b2);

        var conf1 := (pc,stk,s);

        assert code_at(C,pc,compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)) by { resolve_code_at(); }
        var conf2 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|,stk,s);
        assert transitions(C,conf1,conf2) by {
          compile_bexp_correct_true(C, s, b1, pc, 0, |compile_bexp(b2, d1, d0)| + d0, stk);
        }
        assert star<config>(tr,conf1,conf2);

        assert code_at(C,pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|,compile_bexp(b2, d1, d0)) by { resolve_code_at(); }
        var conf3 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)| + |compile_bexp(b2, d1, d0)| + d0,stk,s);
        assert transitions(C,conf2,conf3) by {
          compile_bexp_correct_false(C, s, b2, pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|, d1, d0, stk);
        }
        assert star<config>(tr,conf2,conf3);
        star_trans_sequent<config>(tr,conf1,conf2,conf3);

      } else {

        var conf1 := (pc,stk,s);

        assert code_at(C,pc,compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)) by { resolve_code_at(); }
        var conf2 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)| + |compile_bexp(b2, d1, d0)| + d0,stk,s);
        assert transitions(C,conf1,conf2) by {
          compile_bexp_correct_false(C, s, b1, pc, 0, |compile_bexp(b2, d1, d0)| + d0, stk);
        }
        assert star<config>(tr,conf1,conf2);

      }

    }

  }

}

// Exercise
// Prove that the compilation of commands is correct. Since execution is defined as a least fixed-point, you need to prove this property by transfinite induction.
least lemma compile_com_correct_terminating(s: store, c: com, s': store, C: code, pc: nat, stk: stack)
  requires cexec(s,c,s')
  requires code_at(C,pc,compile_com(c))
  ensures transitions(C,(pc,stk,s),(pc + |compile_com(c)|, stk, s'))
{
  var tr := (c1,c2) => transition(C,c1,c2);
  match c {

    case SKIP =>

    case ASSIGN(id, a) => {
      assert code_at(C,pc,compile_aexp(a)) by { resolve_code_at(); }
      var v := aeval(s,a);
      assert s' == s[id := v];
      var conf1 := (pc,stk,s);
      var conf2 := (pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s);
      assert transitions(C,conf1,conf2) by {
        compile_aexp_correct(C,s,a,pc,stk);
      }
      var conf3 := (pc + |compile_aexp(a)| + 1, stk,s');
      assert transition(C,conf2,conf3);
      star_one_sequent<config>(tr,conf2,conf3);
      star_trans_sequent<config>(tr,conf1,conf2,conf3);
    }

    case SEQ(c1, c2) => {
      var C1 := compile_com(c1);
      var C2 := compile_com(c2);
      var conf1 := (pc,stk,s);
      var conf3 := (pc + |C1| + |C2|,stk,s');
      var si :| cexec(s,c1,si) && cexec(si,c2,s');
      var conf2 := (pc + |C1|,stk,si);
      assert code_at(C,pc,compile_com(c1)) by { resolve_code_at(); }
      compile_com_correct_terminating(s,c1,si,C,pc,stk);
      assert transitions(C,conf1,conf2);
      assert star<config>(tr,conf1,conf2);
      assert code_at(C,pc + |compile_com(c1)|,compile_com(c2)) by { resolve_code_at(); }
      compile_com_correct_terminating(si,c2,s',C,pc + |compile_com(c1)|,stk);
      assert transitions(C,conf2,conf3);
      assert star<config>(tr,conf2,conf3);
      star_trans_sequent<config>(tr,conf1,conf2,conf3);
    }

    case IFTHENELSE(b, if_so, if_not) => {
      assert {:split_here} true;
      var bv := beval(s,b);
      var d1 := 0;
      var code_ifso := compile_com(if_so);
      var d0 := |code_ifso| + 1;
      var code_ifnot := compile_com(if_not);
      var code_prologue := compile_bexp(b,d1,d0);
      var conf1 := (pc,stk,s);

      if beval(s,b) {

        assert code_at(C,pc,compile_bexp(b,0,|code_ifso| + 1)) by { resolve_code_at(); }
        var conf2 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
        assert transitions(C,conf1,conf2) by { compile_bexp_correct_true(C,s,b,pc,d1,d0,stk); }
        assert star<config>(tr,conf1,conf2);

        assert cexec(s,if_so,s');
        assert code_at(C,pc + |compile_bexp(b,d1,d0)| + d1,compile_com(if_so)) by { resolve_code_at(); }

        var conf3 := (pc + |compile_bexp(b,d1,d0)| + d1 + |compile_com(if_so)|, stk, s');
        assert transitions(C,conf2,conf3) by {
          compile_com_correct_terminating(s,if_so,s',C,pc + |compile_bexp(b,d1,d0)| + d1,stk);
        }
        assert star<config>(tr,conf2,conf3);
        star_trans_sequent<config>(tr,conf1,conf2,conf3);

        // Not done yet, we should be facing a branch and need to jump!

        assert C[pc + |compile_bexp(b,d1,d0)| + d1 + |compile_com(if_so)|] == Ibranch(|compile_com(if_not)|);
        var conf4 := (pc + |compile_com(c)|, stk, s');
        assert transition(C,conf3,conf4);
        star_one_sequent<config>(tr,conf3,conf4);
        star_trans_sequent<config>(tr,conf1,conf3,conf4);

      } else {

        assert code_at(C,pc,compile_bexp(b,0,|code_ifso| + 1)) by { resolve_code_at(); }
        var conf2 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
        assert transitions(C,conf1,conf2) by { compile_bexp_correct_false(C,s,b,pc,d1,d0,stk); }
        assert star<config>(tr,conf1,conf2);

        assert cexec(s,if_not,s');
        assert code_at(C,pc + |compile_bexp(b,d1,d0)| + d0,compile_com(if_not)) by { resolve_code_at(); }

        var conf3 := (pc + |compile_bexp(b,d1,d0)| + d0 + |compile_com(if_not)|, stk, s');
        assert transitions(C,conf2,conf3) by {
          compile_com_correct_terminating(s,if_not,s',C,pc + |compile_bexp(b,d1,d0)| + d0,stk);
        }
        assert star<config>(tr,conf2,conf3);
        star_trans_sequent<config>(tr,conf1,conf2,conf3);

      }

    }

    case WHILE(b, body) => {
      assert {:split_here} true;

      var conf1 := (pc,stk,s);
      var d1 := 0;
      var d0 := |compile_com(body)| + 1;

      if beval(s,b) {

        // Simulation of the test
        assert code_at(C,pc,compile_bexp(b,d1,d0)) by { resolve_code_at(); }
        var conf2 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
        assert transitions(C,conf1,conf2) by { compile_bexp_correct_true(C,s,b,pc,d1,d0,stk); }
        assert star<config>(tr,conf1,conf2);

        var si :| cexec(s,body,si) && cexec(si,WHILE(b,body),s');

        // Simulation of the loop body
        var conf3 := (pc + |compile_bexp(b,d1,d0)| + d1 + |compile_com(body)|,stk,si);
        assert code_at(C,pc + |compile_bexp(b,d1,d0)| + d1,compile_com(body)) by { resolve_code_at(); }
        assert transitions(C,conf2,conf3) by {
          compile_com_correct_terminating(s,body,si,C,pc + |compile_bexp(b,d1,d0)| + d1,stk);
        }
        assert star<config>(tr,conf2,conf3);
        star_trans_sequent<config>(tr,conf1,conf2,conf3);

        // Branch back
        assert C[pc + |compile_bexp(b,d1,d0)| + d1 + |compile_com(body)|]
            == Ibranch(-( |compile_bexp(b,d1,d0)| + |compile_com(body)| + 1));
        var conf4 := (pc,stk,si);
        assert transition(C,conf3,conf4);
        star_one_sequent<config>(tr,conf3,conf4);
        star_trans_sequent<config>(tr,conf1,conf3,conf4);

        // And now we have done our due diligence, we simulated one iteration of the loop, and
        // recursively simulate the rest

        var conf5 := (pc + |compile_bexp(b,d1,d0)| + |compile_com(body)| + 1,stk,s');
        assert code_at(C,pc,compile_com(WHILE(b,body))) by { resolve_code_at(); }
        assert transitions(C,conf4,conf5) by {
          compile_com_correct_terminating(si,WHILE(b,body),s',C,pc,stk);
        }
        assert star<config>(tr,conf4,conf5);
        star_trans_sequent<config>(tr,conf1,conf4,conf5);

      } else {

        assert code_at(C,pc,compile_bexp(b,d1,d0)) by { resolve_code_at(); }
        var conf2 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
        assert transitions(C,conf1,conf2) by { compile_bexp_correct_false(C,s,b,pc,d1,d0,stk); }
        assert star<config>(tr,conf1,conf2);

      }

    }
  }
}

// Exercise
// Prove that the compiler is correct and preserves the semantics of the program being compiled.
lemma compile_program_correct_terminating(s: store, c: com, s': store)
  requires cexec(s,c,s')
  ensures machine_terminates(compile_program(c),s,s')
{
  var C := compile_program(c);
  var pc := |C|-1;
  assert pc < |C|;
  assert code_at(C,0,compile_com(c)) by {
    assert C == [] + compile_com(c) + [Ihalt];
  }
  compile_com_correct_terminating(s,c,s',C,0,[]);
  assert transitions(C,(0,[],s),(pc,[],s'));
  assert compile_program(c)[pc] == Ihalt;

}


