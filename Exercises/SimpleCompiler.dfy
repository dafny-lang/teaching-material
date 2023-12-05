// This file was automatically generated from SimpleCompiler.dfy

// In this exercise, you will prove the correctness of a compiler. We need a few definitions to formalize the operational semantics of our source and target language. First, we define 0 or more transitions.
least predicate star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
  (conf1 == conf2) || (exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

// Exercise
// Prove
lemma star_one_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
  requires R(conf1,conf2)
  ensures star(R,conf1,conf2)

// Exercise
// Prove
lemma star_one<T(!new)>()
  ensures forall R: (T,T) -> bool :: forall conf1, conf2: T :: R(conf1,conf2) ==> star(R,conf1,conf2)

// Exercise
// Prove
least lemma star_trans_pre<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
  requires star(R,conf1,conf2)
  ensures  star(R,conf2,conf3) ==> star(R,conf1,conf3)

// Exercise
// Prove
lemma star_trans_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
  requires star(R,conf1,conf2)
  requires star(R,conf2,conf3)
  ensures star(R,conf1,conf3)

// Exercise
// Prove
lemma star_trans<T(!new)>()
  ensures forall R: (T,T) -> bool :: forall conf1, conf2, conf3: T :: (star(R,conf1,conf2) && star(R,conf2,conf3)) ==> star(R,conf1,conf3)

// A transition that makes at least one step.
least predicate plus<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
  (exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

// Exercise
// Prove
lemma plus_one<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
  requires R(conf1,conf2)
  ensures star(R,conf1,conf2)

// Exercise
// Prove
lemma plus_star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
  requires plus(R,conf1,conf2)
  ensures star(R,conf1,conf2)

// Exercise
// Prove
lemma star_plus_trans<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
  requires star(R,conf1,conf2)
  requires plus(R,conf2,conf3)
  ensures plus(R,conf1,conf3)

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

// Exercise
// Define a sequence of transitions.
ghost predicate transitions(C: code, conf1: config, conf2: config) 

// Exercise
// Define termination for an assembly execution.
ghost predicate machine_terminates(C: code, s_init: store, s_final: store) 

// Exercise
// Define a function that compiles an arithmetic expression to assembly code.
function compile_aexp(a: aexp): code 

// Exercise
// Define a function that compiles a Boolean expression to assembly code.
function compile_bexp(b: bexp, d1: int, d0: int): code 

// Exercise
// Define a function that compiles a command to assembly code.
function compile_com(c: com): code 

// Exercise
// Define the compilation of an entire program to assembly code.
function compile_program(p: com): code 

// The following predicates allows us to structure the assemble code, it will be very handy.
ghost predicate code_at(C: code, pc: nat, C2: code) {
  exists C1, C3: code :: C == C1 + C2 + C3 && |C1| == pc
}

// Exercise
// Prove.
lemma code_at_app_left(C: code, pc: nat, C1: code, C2: code)
  requires code_at(C,pc,C1 + C2)
  ensures code_at(C,pc,C1)

// Exercise
// Prove.
lemma code_at_app_right(C: code, pc: nat, C1: code, C2: code)
  requires code_at(C,pc,C1 + C2)
  ensures code_at(C,pc + |C1|,C2)

// Exercise
// Prove.
lemma resolve_code_at()
  ensures forall C: code :: forall pc: nat :: forall C1, C2: code :: code_at(C,pc,C1 + C2) ==> code_at(C,pc,C1)
  ensures forall C: code :: forall pc: nat :: forall C1, C2: code :: code_at(C,pc,C1 + C2) ==> code_at(C,pc + |C1|,C2)

// Exercise
// Prove that the compilation of arithmetic expressions is correct.
lemma compile_aexp_correct(C: code, s: store, a: aexp, pc: nat, stk: stack)
  requires forall id: ident :: id_in_aexp(id,a) ==> id in s
  requires code_at(C,pc,compile_aexp(a))
  ensures transitions(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s))

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

// Exercise
// Second part of the proof.
lemma compile_bexp_correct_false(C: code, s: store, b: bexp, pc: nat, d1: nat, d0: nat, stk: stack)
  requires forall id: ident :: id_in_bexp(id,b) ==> id in s
  requires code_at(C,pc,compile_bexp(b,d1,d0))
  requires !beval(s,b)
  ensures transitions(C,(pc,stk,s),(pc + (|compile_bexp(b,d1,d0)| + d0), stk, s))

// Exercise
// Prove that the compilation of commands is correct. Since execution is defined as a least fixed-point, you need to prove this property by transfinite induction.
least lemma compile_com_correct_terminating(s: store, c: com, s': store, C: code, pc: nat, stk: stack)
  requires cexec(s,c,s')
  requires code_at(C,pc,compile_com(c))
  ensures transitions(C,(pc,stk,s),(pc + |compile_com(c)|, stk, s'))

// Exercise
// Prove that the compiler is correct and preserves the semantics of the program being compiled.
lemma compile_program_correct_terminating(s: store, c: com, s': store)
  requires cexec(s,c,s')
  ensures machine_terminates(compile_program(c),s,s')


