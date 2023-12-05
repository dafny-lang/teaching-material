
// Exercise
// Implement the following method to satisfy this specification.
method Mystery(a: array<int>, i: nat, j: nat)
  modifies a
  requires i < a.Length && j < a.Length
  ensures old(a[i]) == a[j] && old(a[j]) == a[i]
{
  var tmp: int := a[i];
  a[i] := a[j];
  a[j] := tmp;
}

// Consider the following definition of a reference.
type ref<T> = a: array<T> | a.Length == 1 witness *

// And the definition of an even natural number
ghost predicate Even(a: nat) {
  exists b: nat :: a == 2 * b
}

// Exercise
//  Implement and verify the following method to satisfy its postcondition.
method Arbitrary(s: ref<nat>)
  modifies s
  ensures s[0] == 4 * old(s[0]) * old(s[0])
  ensures Even(s[0])
{

  s[0] := 2 * s[0];

  label L1: assert Even(s[0]);

  s[0] := s[0] * s[0];

  assert Even(s[0]) by {
    assert exists b: nat :: s[0] == 2 * b by {
      assert exists c: nat :: old@L1(s[0]) == 2 * c;
      var c: nat :| old@L1(s[0]) == 2 * c;
      assert s[0] == old@L1(s[0]) * old@L1(s[0]);
      assert s[0] == (2 * c) * (2 * c);
      assert s[0] == 2 * (2 * c * c);
    }
  }

}

// Exercise
// Implement and verify a method that goes over an array and for all index i, sets a[i] to a[i].
method DoNothing(a: array<int>)
  modifies a
  ensures forall i: nat :: i < a.Length ==> old(a[i]) == a[i]
{
  for i := 0 to a.Length
    invariant i <= a.Length
    invariant forall j: nat :: j < i ==> old(a[j]) == a[j]
    invariant forall j: nat :: i <= j < a.Length ==> old(a[j]) == a[j]
  {
    a[i] := a[i];
  }
}

