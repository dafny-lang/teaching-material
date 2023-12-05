
// In this exercise, you will implement and verify an LRU cache. We use the following definition of a Cell.
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

// Assume the following implementation of a doubly-linked list.
class DoublyLinkedList<T> {

  ghost var Repr: set<Cell<T>>;

  constructor()

  method enqueue(v: T) returns (it: Cell<T>)
    modifies this, Repr
    ensures Repr == {it} + old(Repr)
    ensures fresh(it)
    ensures forall it: Cell<T> :: it in old(Repr) ==> it.value == old(it.value)
    ensures it.value == v

}

// Specification of an LRU cache.
trait LRUCacheSpec<T> {

  var storage: map<nat,T>
  var queue: DoublyLinkedList<(nat,T)>

  ghost predicate Invariant()
    reads this, queue, queue.Repr

  method get(key: nat) returns (result: Outcome<T>)
    modifies this, queue, queue.Repr
    requires Invariant()
    ensures Invariant()
    ensures key in storage ==> result.Success? && result.value == storage[key]
    ensures result.Failure? ==> key !in storage

  method put(key: nat, value: T)
    modifies this, queue.Repr
    requires Invariant()
    ensures Invariant()

}

// Exercise
// Implement the LRU cache trait.
class LRUCache<T> extends LRUCacheSpec<T>
{

  const cache_size: nat

  var cache: map<nat,Cell<(nat,T)>>

  ghost predicate Invariant()
    reads this, queue, queue.Repr
  {

    && (forall key: nat :: key in cache ==> cache[key] in queue.Repr)
    && (forall key, key': nat :: key in cache && key' in cache && key != key' ==> cache[key] != cache[key'])
    && (forall key: nat :: key in cache ==> key in storage && cache[key].value.1 == storage[key])

  }

  constructor(size: nat)
    requires size >= 2
    ensures Invariant()
  {
    cache_size := size;
    storage := map[];
    cache := map[];
    queue := new DoublyLinkedList<(nat,T)>();
  }

  method get(key: nat) returns (result: Outcome<T>)
    modifies this, queue, queue.Repr
    requires Invariant()
    ensures Invariant()
    ensures key in storage ==> result.Success? && result.value == storage[key]
    ensures result.Failure? ==> key !in storage
  {
    if key in cache {
      result := Success(cache[key].value.1);

      var c := cache[key];

    } else if key in storage {
      var value: T := storage[key];
      result := Success(value);

      var c := queue.enqueue((key,value));
      cache := cache[key := c];

    } else {
      result := Failure;
    }
  }

  method put(key: nat, value: T)
    modifies this, queue.Repr
    requires Invariant()
    ensures Invariant()
  {
    storage := storage[key := value];
    if key in cache {
      cache[key].value := (key,value);
    }
  }

}

