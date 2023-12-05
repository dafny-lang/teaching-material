// This file was automatically generated from DoublyLinkedList.dfy

// In this exercise we will implement part of a queue as a doubly-linked list. We use the following definition of a Cell.
class Cell<T> {

  var prev: Cell?<T>
  var next: Cell?<T>
  var value: T

  constructor(value: T)
    ensures this.value == value
    ensures this.prev == null
    ensures this.next == null
  {

    this.value := value;
    prev := null;
    next := null;

  }

}

// Definition of outcomes.
datatype Outcome<T> =
  | Success(value: T)
  | Failure

// Specification of a Queue.
trait Queue<T> {

  ghost var Repr: seq<Cell<T>>;

  ghost predicate Invariant()
    reads this, Repr

  method enqueue(v: T) returns (it: Cell<T>)
    modifies this, Repr
    requires Invariant()
    ensures Invariant()
    ensures Repr == [it] + old(Repr)
    ensures fresh(it)
    ensures forall it: Cell<T> :: it in old(Repr) ==> it.value == old(it.value)
    ensures it.value == v

}

// Exercise
// Implement a Queue as a doubly-linked list.
class DoublyLinkedList<T> extends Queue<T>

