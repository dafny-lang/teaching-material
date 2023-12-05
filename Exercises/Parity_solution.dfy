// A natural is *even* if it is a multiple of 2.
ghost predicate even(a: nat) {
  exists b: nat :: a == 2 * b
}

// A natural is *odd* if it is not even.
ghost predicate odd(a: nat) {
  !even(a)
}

// Exercise
// Prove that the square of an even natural is even.
lemma even_prop_1()
  ensures forall n: nat :: even(n) ==> even(n * n)
{
  forall n: nat ensures even(n) ==> even(n * n) {
    if even(n) {
      var a: nat :| n == 2 * a;
      assert n * n == 2 * (2 * a * a);
    }
  }
}

// Exercise
// Prove that the sum of two even naturals is even.
lemma even_prop_2()
  ensures forall n: nat, m: nat :: even(n) && even(m) ==> even(n + m)
{
  forall n: nat, m: nat ensures even(n) && even(m) ==> even(n + m) {
    if even(n) && even(m) {
      var a: nat :| n == 2 * a;
      var b: nat :| m == 2 * b;
      assert n + m == 2 * (a + b);
    }
  }
}

// Exercise
// Prove that a number is odd if and only if it is 1 plus a multiple of 2.
lemma odd_representation(a: nat)
  ensures odd(a) <==> exists b: nat :: a == 2 * b + 1
{
  if a == 0 {
    assert 0 == 2 * 0;
  }
  else if a == 1 {
    assert a == 2 * 0 + 1;
  }
  else {
    if odd(a-1) {
      odd_representation(a-1);
      var p :| a-1 == 2 * p + 1;
      assert a == 2 * (p + 1);
    }
    else {
      odd_representation(a-2);
    }
  }
}

// Exercise
// Prove that if a square natural is even, so is its square root.
lemma square_even(n: nat)
  requires even(n * n)
  ensures even(n)
{
  if !even(n) {
    odd_representation(n);
    assert exists a: nat :: n == 2 * a + 1;
    var a :| n == 2 * a + 1;
    assert n * n == 2 * (2 * a * a + 2 * a) + 1;
    assert odd(n*n);
  }
}
