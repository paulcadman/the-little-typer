Require Import Vector Arith Bool List Nat.

(** Exercises for Chapter 15 of The Little Typer *)

(** Remove the following axiom when you've finished all the exercises. This
axoim provides a value of any type to allow the file to compile and incomplete
expressions to be used.
 *)
Axiom fill_me : forall {X : Type}, X.

(** Exercise 15.C1

Prove that any natural number is not equal to its sucessor.

Hints:

1. The following facts are available in the library:

[[
   O_S: forall n : nat, 0 <> S n

   eq_add_S: forall n m : nat, S n = S m -> n = m
]] 

You can find these facts using:

[[
   Search (0 = S _).
   Search (S _ = S _ -> _ = _).
]]

2. The notation <> corresponds to not. You can find this out using:
[[
   Locate "<>".
]]
 *)

Lemma n_not_S_n : forall n, n <> S n.
Proof.
  exact fill_me.
Qed.


(** Exercise 15.C2

Using induction on a Vector, define a function called [rest] that
accepts any non-nil vector and returns a new vector with the first element
removed.

Hint:

Have a look at the definition of [front] in coq/ch15.v (relative to the root
of this repository).

Try to use the [induction] tactic on a vector. You'll probably need to define
an auxilliary function that plays the same role as the nested [ind-Vec] in
frame 15.74 of the book.
 *)

Definition rest : forall E l, Vector.t E (S l) -> Vector.t E l.
  exact fill_me.
Qed.

(** Exercise 15.C3

Prove that the Principle of the Excluded Middle is equivalent to using double
negation to prove a proposition.

Hint:

Have a look at the definition of [pem] in coq/ch15.v (relative to the root
of this repository). Though for these Theorems you'll probably want to use
tactics rather than an explicit lambda.
*)

Theorem pem_double_neg : forall X, (X \/ ~ X) -> (~~ X) -> X.
Proof.
  exact fill_me.
Qed.

Theorem double_neg_pem : forall X, (~~ X) -> X -> (X \/ ~ X).
Proof.
  exact fill_me.
Qed.
