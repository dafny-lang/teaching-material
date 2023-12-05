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
{
  if l.Nil? then 0 else 1 + len(l.tl)
}

// Exercise
// Define a function that concatenates or appends two lists.
function app<T>(l1: list, l2: list): list
{
  match l1 {
    case Nil => l2
    case Cons(e,l) => Cons(e,app(l,l2))
  }
}

// Exercise
// Define a function that gets a value at some position in the list.
function at<T>(l: list, index: nat): option
{
  match l {
    case Nil => None
    case Cons(e,l) =>
      if index == 0 then Some(e) else at(l,index-1)
  }
}

// Exercise
// Prove.
lemma app_decomposition<T>(l1: list, l2: list, l3: list, l4: list)
  requires len(l1) == len(l3)
  requires app(l1,l2) == app(l3,l4)
  ensures l1 == l3 && l2 == l4
{
  match (l1, l3) {
    case (Nil,Nil) =>
    case (Cons,Nil) =>
    case (Nil, Cons) =>
    case (Cons(e1,l1),Cons(e3,l3)) => {
      app_decomposition(l1,l2,l3,l4);
    }
  }
}

// Exercise
// Prove.
lemma at_prop_1<T>(l: list, idx: nat)
  requires idx < len(l)
  ensures exists v: T :: at(l,idx) == Some(v)
{
  match l {
    case Nil =>
    case Cons(e,l) => {
      if idx == 0 {
        assert at(Cons(e,l),0) == Some(e);
      } else {
        at_prop_1(l,idx-1);
      }
    }
  }
}

// Exercise
// Prove.
function reverse'<T>(l: list, acc: list): list
{
  match l {
    case Nil => acc
    case Cons(e,l) => reverse'(l,Cons(e,acc))
  }
}

// Exercise
// Prove.
function reverse<T>(l: list): list
{
  reverse'(l,Nil)
}

// Exercise
// Prove.
lemma reverse_app_pre<T>(l1: list, l2: list, acc: list)
  ensures reverse'(l1,app(l2,acc)) == app(reverse'(l1,l2),acc)
{
}

// Exercise
// Prove.
lemma reverse_app'<T>(l1: list, l2: list, acc: list)
  ensures reverse'(app(l1,l2),acc) == app(reverse'(l2,Nil),reverse'(l1,acc))
{
  match l1 {
    case Nil => {
      reverse_app_pre(l2,Nil,acc);
    }
    case Cons(e, l) => {
    }
  }
}

// Exercise
// Prove.
lemma reverse_app<T>(l1: list, l2: list)
  ensures reverse(app(l1,l2)) == app(reverse(l2),reverse(l1))
{
  reverse_app'(l1,l2,Nil);
}

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
{
  forall idx: nat, v: T :: idx < len(l) && at(l,idx) == Some(v) ==> P(v)
}

// Exercise
// Prove.
lemma all_true_no_order_prop<T(!new)>(e: T, l: list, P: T -> bool)
  requires all_true_no_order(Cons(e,l),P)
  ensures all_true_no_order(l,P)
{
  forall idx: nat, v: T ensures idx < len(l) && at(l,idx) == Some(v) ==> P(v) {
    if idx < len(l) && at(l,idx) == Some(v) {
      assert idx < len(Cons(e,l));
      assert at(Cons(e,l),idx+1) == Some(v);
    }
  }
}

// Exercise
// Prove.
lemma all_true_forward_no_order_1'<T(!new)>(l: list, P: T -> bool, b: bool)
  requires all_true_forward'(l,P,b)
  ensures b && all_true_no_order(l,P)
{
}

// Exercise
// Prove.
lemma all_true_forward_no_order_1<T(!new)>(l: list, P: T -> bool)
  requires all_true_forward(l,P)
  ensures all_true_no_order(l,P)
{
  all_true_forward_no_order_1'(l,P,true);
}

// Exercise
// Prove.
lemma all_true_forward_no_order_2<T(!new)>(l: list, P: T -> bool)
  requires all_true_no_order(l,P)
  ensures all_true_forward(l,P)
{
  match l {
    case Nil =>
    case Cons(e,l) => {
      assert P(e) by {
        at_prop_1(Cons(e,l),0);
        var v0 :| at(Cons(e,l),0) == Some(v0) && P(v0);
      }
      all_true_no_order_prop(e,l,P);
      all_true_forward_no_order_2(l,P);
    }
  }
}

// Exercise
// Prove.
lemma all_true_backward_no_order_1<T(!new)>(l: list, P: T -> bool)
  requires all_true_backward(l,P)
  ensures all_true_no_order(l,P)
{
}

// Exercise
// Prove.
lemma all_true_backward_no_order_2<T(!new)>(l: list, P: T -> bool)
  requires all_true_no_order(l,P)
  ensures all_true_backward(l,P)
{
  match l {
    case Nil =>
    case Cons(e,l) => {
      assert P(e) by {
        at_prop_1(Cons(e,l),0);
        var v0 :| at(Cons(e,l),0) == Some(v0) && P(v0);
      }
      all_true_no_order_prop(e,l,P);
      all_true_backward_no_order_2(l,P);
    }
  }
}

// Exercise
// Prove.
lemma all_true_same<T(!new)>(P: T -> bool)
  ensures forall l: list<T> :: all_true_forward(l,P) <==> all_true_backward(l,P)
{
  forall l: list<T> ensures all_true_forward(l,P) <==> all_true_backward(l,P) {
    if all_true_forward(l,P) {
      all_true_forward_no_order_1(l,P);
      all_true_backward_no_order_2(l,P);
    }
    if all_true_backward(l,P) {
      all_true_backward_no_order_1(l,P);
      all_true_forward_no_order_2(l,P);
    }
  }
}

