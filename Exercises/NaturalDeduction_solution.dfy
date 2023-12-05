
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
{
}

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
{
    premise_1();
    premise_2();
}

}

module conjunction_elimination_1 {

  import opened Setup

  lemma premise()
    ensures A() && B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A()
{
    premise();
}

}

module conjunction_elimination_2 {

  import opened Setup

  lemma premise()
    ensures A() && B()

// Exercise
// Prove.
  lemma conclusion()
    ensures B()
{
    premise();
}

}

module disjunction_introduction_1 {

  import opened Setup

  lemma premise()
    ensures A()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() || B()
{
    premise();
}

}

module disjunction_introduction_2 {

  import opened Setup

  lemma premise()
    ensures B()

// Exercise
// Prove.
  lemma conclusion()
    ensures A() || B()
{
    premise();
}

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
{
    premise_1();
    if A() {
      premise_2();
    }
    if B() {
      premise_3();
    }
}

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
{
    if A() {
      premise();
    }
}

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
{
    premise_1();
    premise_2();
}

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
{
    if A() {
      premise();
    }
}

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
{
    if A() {
      premise_2();
    }
    premise_1();
}

}

module false_elimination {

  import opened Setup

  lemma premise()
    ensures false

// Exercise
// Prove.
  lemma conclusion()
    ensures A()
{
    premise();
}

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
{
    forall x { premise(x); }
}

}

module universal_elimination {

  import opened Setup

  lemma premise()
    ensures forall x: t :: P(x)

// Exercise
// Prove.
  lemma conclusion()
    ensures P(k)
{
    premise();
}

}

module existential_introduction {

  import opened Setup

  lemma premise()
    ensures P(k)

// Exercise
// Prove.
  lemma conclusion()
    ensures exists x: t :: P(x)
{
    premise();
}

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
{
    premise_1();
    var x: t :| P(x);
    if P(x) {
      premise_2(x);
    }
}

}
