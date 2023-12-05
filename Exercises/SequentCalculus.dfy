// This file was automatically generated from SequentCalculus.dfy

// In this exercise, you will encode all the rules of sequent calculus in Dafny. To this end, we will use a few symbols. In what follows, every module correspond to one rule of sequent calculus. Each of these rules has 0 or more premises, which are declared as axioms, and a conclusion, that you need to prove.
module Setup {

  type t(00)

  ghost predicate A()
  ghost predicate B()
  ghost predicate C()
  ghost predicate P(x: t)

  ghost const k: t

}

module axiom {

  import opened Setup

// Exercise
// Prove.
  lemma conclusion()
    requires A()
    ensures A()

}


module cut {

  import opened Setup

  lemma premise_1()
    ensures A()

  lemma premise_2()
    requires A()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    ensures B()

}

module weakening {

  import opened Setup

  lemma premise()
    ensures A()

// Exercise
// Prove.
  lemma conclusion()
    requires B()
    ensures A()

}

module permutation {

  import opened Setup

  lemma premise()
    requires A()
    requires B()
    ensures C()

// Exercise
// Prove.
  lemma conclusion()
    requires B()
    requires A()
    ensures C()

}

module contraction {

  import opened Setup

  lemma premise()
    requires A()
    requires A()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    requires A()
    ensures B()

}

module conjunction_right {

  import opened Setup

  lemma premise_1()
    ensures A()

  lemma premise_2()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() && B()

}

module conjunction_left {

  import opened Setup

  lemma premise_1()
    ensures A()

  lemma premise_2()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() && B()

}

module disjunction_right_1 {

  import opened Setup

  lemma premise()
    ensures A()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() || B()

}

module disjunction_right_2 {

  import opened Setup

  lemma premise()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() || B()

}

module disjunction_left {

  import opened Setup

  lemma premise_1()
    requires A()
    ensures C()

  lemma premise_2()
    requires B()
    ensures C()

// Exercise
// Prove.
  lemma conclusion()
    requires A() || B()
    ensures C()

}

module implication_right {

  import opened Setup

  lemma premise()
    requires A()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() ==> B()

}

module implication_left {

  import opened Setup

  lemma premise_1()
    ensures A()

  lemma premise_2()
    requires B()
    ensures C()

// Exercise
// Prove.
  lemma conclusion()
    requires A() ==> B()
    ensures C()

}

module negation_right {

  import opened Setup

  lemma premise()
    requires A()
    ensures false

// Exercise
// Prove.
  lemma conclusion()
    ensures ! A()

}

module negation_left {

  import opened Setup

  lemma premise()
    ensures A()

// Exercise
// Prove.
  lemma conclusion()
    requires ! A()
    ensures B()

}

module false_left {

  import opened Setup

// Exercise
// Prove.
  lemma conclusion()
    requires false
    ensures A()

}

module universal_right {

  import opened Setup

  lemma premise(x: t)
    ensures P(x)

// Exercise
// Prove.
  lemma conclusion()
    ensures forall x: t :: P(x)

}

module universal_left {

  import opened Setup

  lemma premise()
    requires P(k)
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    requires forall x: t :: P(x)
    ensures B()

}

module existential_right {

  import opened Setup

  lemma premise()
    ensures P(k)

// Exercise
// Prove.
  lemma conclusion()
    ensures exists x: t :: P(x)

}

module existential_left {

  import opened Setup

  lemma premise(x: t)
    requires P(x)
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    requires exists x: t :: P(x)
    ensures B()

}

