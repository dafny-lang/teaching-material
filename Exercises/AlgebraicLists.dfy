// This file was automatically generated from AlgebraicLists.dfy
// Verified implementation of the classic algebraic lists.
datatype list<T> =
  | Nil
  | Cons(hd: T, tl: list)

// We will use an option type
datatype option<T> =
  | Some(value: T)
  | None

// Exercise
// Define a function that computes the length of a list.
function len<T>(l: list): nat

// Exercise
// Define a function that concatenates or appends two lists.
function app<T>(l1: list, l2: list): list

// Exercise
// Define a function that gets a value at some position in the list.
function at<T>(l: list, index: nat): option

// Exercise
// Prove.
lemma app_decomposition<T>(l1: list, l2: list, l3: list, l4: list)
  requires len(l1) == len(l3)
  requires app(l1,l2) == app(l3,l4)
  ensures l1 == l3 && l2 == l4

// Exercise
// Prove.
lemma at_prop_1<T>(l: list, idx: nat)
  requires idx < len(l)
  ensures exists v: T :: at(l,idx) == Some(v)

// Exercise
// Prove.
function reverse'<T>(l: list, acc: list): list

// Exercise
// Prove.
function reverse<T>(l: list): list

// Exercise
// Prove.
lemma reverse_app_pre<T>(l1: list, l2: list, acc: list)
  ensures reverse'(l1,app(l2,acc)) == app(reverse'(l1,l2),acc)

// Exercise
// Prove.
lemma reverse_app'<T>(l1: list, l2: list, acc: list)
  ensures reverse'(app(l1,l2),acc) == app(reverse'(l2,Nil),reverse'(l1,acc))

// Exercise
// Prove.
lemma reverse_app<T>(l1: list, l2: list)
  ensures reverse(app(l1,l2)) == app(reverse(l2),reverse(l1))

// Consider the following predicates over lists
predicate all_true_forward'<T(!new)>(l: list, P: T -> bool, b: bool) {
  match l {
    case Nil => b
    case Cons(e,l) => all_true_forward'(l,P, b && P(e))
  }
}

// Checking that a property holds for every element of the list, going forward.
predicate all_true_forward<T(!new)>(l: list, P: T -> bool) {
  all_true_forward'(l,P,true)
}

// Checking that a property holds for every element of the list, going backward.
predicate all_true_backward<T(!new)>(l: list, P: T -> bool) {
  match l {
    case Nil => true
    case Cons(e,l) => P(e) && all_true_backward(l,P)
  }
}

// Exercise
// The goal is to prove that the two methods agree. Following is a very structured proof, and you need not follow it. If you want, you can prove this much more succintely. To start, define a predicate that does not impose any order.
ghost predicate all_true_no_order<T(!new)>(l: list, P: T -> bool)

// Exercise
// Prove.
lemma all_true_no_order_prop<T(!new)>(e: T, l: list, P: T -> bool)
  requires all_true_no_order(Cons(e,l),P)
  ensures all_true_no_order(l,P)

// Exercise
// Prove.
lemma all_true_forward_no_order_1'<T(!new)>(l: list, P: T -> bool, b: bool)
  requires all_true_forward'(l,P,b)
  ensures b && all_true_no_order(l,P)

// Exercise
// Prove.
lemma all_true_forward_no_order_1<T(!new)>(l: list, P: T -> bool)
  requires all_true_forward(l,P)
  ensures all_true_no_order(l,P)

// Exercise
// Prove.
lemma all_true_forward_no_order_2<T(!new)>(l: list, P: T -> bool)
  requires all_true_no_order(l,P)
  ensures all_true_forward(l,P)

// Exercise
// Prove.
lemma all_true_backward_no_order_1<T(!new)>(l: list, P: T -> bool)
  requires all_true_backward(l,P)
  ensures all_true_no_order(l,P)

// Exercise
// Prove.
lemma all_true_backward_no_order_2<T(!new)>(l: list, P: T -> bool)
  requires all_true_no_order(l,P)
  ensures all_true_backward(l,P)

// Exercise
// Prove.
lemma all_true_same<T(!new)>(P: T -> bool)
  ensures forall l: list<T> :: all_true_forward(l,P) <==> all_true_backward(l,P)

