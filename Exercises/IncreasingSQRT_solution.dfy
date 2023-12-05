
// In this exercise, we will prove some properties of the square root function. First, we posit its existence.
ghost function Sqrt(x: real): real

// The square root function is characterized by two properties that we axiomatize. First, the square root function is positive.
lemma SqrtPos()
  ensures forall x: real :: x >= 0.0 ==> Sqrt(x) >= 0.0

// Second, for a given real x, the product of the square root of x with itself is x. That's the essence of the square root function.
lemma SqrtProp()
  ensures forall x: real :: x >= 0.0 ==> Sqrt(x) * Sqrt(x) == x

// Exercise
// Our goal is to prove that the square root function is monotonic. First, we will do so as a sequent. Maybe you do not remember how to prove this property, and that's fine. Think about it on paper first, and when you think you might have an argument, see if Dafny accepts it. Hint: assume that the square root function was not monotonic, and show that it is inconsistent.
lemma MonotonicPre(x: real, y: real)
  requires 0.0 <= x < y
  ensures Sqrt(x) < Sqrt(y)
{
  assert x < y;
  assert Sqrt(x) * Sqrt(x) < Sqrt(y) * Sqrt(y) by {
    SqrtProp();
  }
  assert Sqrt(x) >= 0.0 && Sqrt(y) >= 0.0 by {
    SqrtPos();
  }
  if Sqrt(x) >= Sqrt(y) {
    assert Sqrt(x) * Sqrt(x) >= Sqrt(y) * Sqrt(y);
    assert false;
  }
}

// Exercise
// Using that lemma we just proved, prove the non-sequent version of the theorem.
lemma Monotonic()
  ensures forall x, y: real :: 0.0 <= x < y ==> Sqrt(x) < Sqrt(y)
{
  forall x, y: real ensures 0.0 <= x < y ==> Sqrt(x) < Sqrt(y) {
    if 0.0 <= x < y {
      MonotonicPre(x,y);
    }
  }
}

