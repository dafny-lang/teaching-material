// This file was automatically generated from NaturalDeduction.dfy

// In this exercise, you will encode all the rules of natural deduction in Dafny. To this end, we will use a few symbols. In what follows, every module correspond to one rule of natural deduction. Each of these rules has 0 or more premises, which are declared as axioms, and a conclusion, that you need to prove.
module Setup {

  type t(00)

  predicate A()
  predicate B()
  predicate C()
  predicate P(x: t)

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

module conjunction_introduction {

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

module conjunction_elimination_1 {

  import opened Setup

  lemma premise()
    ensures A() && B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A()

}

module conjunction_elimination_2 {

  import opened Setup

  lemma premise()
    ensures A() && B()

// Exercise
// Prove.
  lemma conclusion()
    ensures B()

}

module disjunction_introduction_1 {

  import opened Setup

  lemma premise()
    ensures A()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() || B()

}

module disjunction_introduction_2 {

  import opened Setup

  lemma premise()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() || B()

}

module disjunction_elimination {

  import opened Setup

  lemma premise_1()
    ensures A() || B()

  lemma premise_2()
    requires A()
    ensures C()

  lemma premise_3()
    requires B()
    ensures C()

// Exercise
// Prove.
  lemma conclusion()
    ensures C()

}

module implication_introduction {

  import opened Setup

  lemma premise()
    requires A()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() ==> B()

}

module implication_elimination {

  import opened Setup

  lemma premise_1()
    ensures A() ==> B()

  lemma premise_2()
    ensures A()

// Exercise
// Prove.
  lemma conclusion()
    ensures B()

}

module negation_introduction {

  import opened Setup

  lemma premise()
    requires A()
    ensures false

// Exercise
// Prove.
  lemma conclusion()
    ensures ! A()

}

module negation_elimination {

  import opened Setup

  lemma premise_1()
    ensures A()

  lemma premise_2()
    ensures ! A()

// Exercise
// Prove.
  lemma conclusion()
    ensures false

}

module false_elimination {

  import opened Setup

  lemma premise()
    ensures false

// Exercise
// Prove.
  lemma conclusion()
    ensures A()

}

module universal_introduction {

  import opened Setup

  lemma premise(x: t)
    // x cannot appear freely in the environment, or it means we have additional assumptions!
    ensures P(x)

// Exercise
// Prove.
  lemma conclusion()
    ensures forall x: t :: P(x)

}

module universal_elimination {

  import opened Setup

  lemma premise()
    ensures forall x: t :: P(x)

// Exercise
// Prove.
  lemma conclusion()
    ensures P(k)

}

module existential_introduction {

  import opened Setup

  lemma premise()
    ensures P(k)

// Exercise
// Prove.
  lemma conclusion()
    ensures exists x: t :: P(x)

}

module existential_elimination {

  import opened Setup

  lemma premise_1()
    ensures exists x: t :: P(x)

  lemma premise_2(x: t)
    requires P(x)
    ensures A()

// Exercise
// Prove.
  lemma conclusion()
    ensures A()

}
