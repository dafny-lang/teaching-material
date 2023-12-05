
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
{

  var head: Cell?<T>
  var tail: Cell?<T>
  var size: nat

  ghost predicate Invariant()
    reads this, Repr
  {
    && (|Repr| == size)
    && (size >= 1 <==> head != null && tail != null)
    && (size >= 1 ==> head == Repr[0] && tail == Repr[size-1])
  }

  constructor()
    ensures Invariant()
    ensures size == 0
  {
    head := null;
    tail := null;
    Repr := [];
    size := 0;
  }

  method enqueue(v: T) returns (it: Cell<T>)
    modifies this, Repr
    requires Invariant()
    ensures Invariant()
    ensures Repr == [it] + old(Repr)
    ensures fresh(it)
    ensures forall it: Cell<T> :: it in old(Repr) ==> it.value == old(it.value)
    ensures it.value == v
  {
    if size == 0 {
      var it: Cell := new Cell(v);
      Repr := [it];
      size := 1;
      head := it;
      tail := it;
      return it;
    } else if size == 1 {
      var it: Cell := new Cell(v);
      Repr := [it] + Repr;
      size := size + 1;
      head := it;
      head.next := tail;
      tail.prev := head;
      return it;
    } else {
      var it: Cell := new Cell(v);
      Repr := [it] + Repr;
      size := size + 1;
      var old_head := head;
      head := it;
      head.next := old_head;
      old_head.prev := head;
      return it;
    }
  }

}

