// In this exercise, we prove that the function that computes triangular numbers has a closed form definition. First we posit its existence.
ghost function TriangleSum(n: nat): nat

// We now posit axioms that define the behavior of that function. First, the triangle sum of 0 is zero.
lemma TriangleSumBase()
  ensures TriangleSum(0) == 0

// Second, the triangle sum of n + 1 is the triangle sum of n, plus n. (That is, a triangle with n blocks at its base that we place on top of a layer of n + 1 blocks.)
lemma TriangleSumRec()
  ensures forall n: nat :: n > 0 ==> TriangleSum(n) == n + TriangleSum(n-1)

// Exercise
// Prove that the triangle sum has a closed form solution.
lemma GaussTrickSeq(n: nat)
  ensures TriangleSum(n) == (n * (n + 1)) / 2
{
  if n == 0 {
    TriangleSumBase();
  } else {
    assert TriangleSum(n) == n + TriangleSum(n-1) by {
      TriangleSumRec();
    }
    GaussTrickSeq(n-1);
  }
}

// Exercise
// Prove it again in quantified form.
lemma GaussTrick()
  ensures forall n: nat :: TriangleSum(n) == (n * (n + 1)) / 2
{
  forall n: nat ensures TriangleSum(n) == (n * (n + 1)) / 2 {
    GaussTrickSeq(n);
  }
}

