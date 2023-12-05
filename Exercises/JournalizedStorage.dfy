// This file was automatically generated from JournalizedStorage.dfy

// Implement the following trait that specifies the API of a journalized storage.
datatype Outcome<T> =
  | Success(value: T)
  | Failure

datatype entry<T> = Entry(key: nat,value: T)

trait Storage<T(!new)> {

  ghost var log: seq<entry<T>>

  function last_occurrence_pre(key: nat, log': seq<entry<T>>): Outcome<T> {
    var size: nat := |log'|;
    if size == 0 then
      Failure
    else
      var candidate: entry := log'[size-1];
      if candidate.key == key then
        Success(candidate.value)
      else
        last_occurrence_pre(key, log'[..(size-1)])
  }

  ghost function last_occurrence(key: nat): Outcome<T>
    reads this
  {
    last_occurrence_pre(key,log)
  }

  ghost predicate Invariant()
    reads this

  method get(key: nat) returns (result: Outcome<T>)
    requires Invariant()
    ensures Invariant()
    ensures result.Success? <==> exists index: nat :: index < |log| && log[index].key == key
    ensures result.Success? ==> last_occurrence(key).Success? && last_occurrence(key).value == result.value

  function fget(key: nat): Outcome<T>
    reads this
    requires Invariant()

  method put(key: nat, value: T)
    modifies this
    requires Invariant()
    ensures log == old(log) + [Entry(key,value)]
    ensures Invariant()

}

// Exercise
// Implement the Storage trait
class MapStorage<T(!new)> extends Storage<T> 

