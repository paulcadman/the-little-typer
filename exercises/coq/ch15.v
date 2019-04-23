Require Import Vector Arith Bool List Nat.

(** Exercises for Chapter 15 of The Little Typer *)

(** Remove the following axiom when you've finished all the exercises. This
axoim provides a value of any type to allow the file to compile and incomplete
expressions to be used.
 *)
Axiom fill_me : forall {X : Type}, X.

Definition leq : nat -> nat -> Prop :=
  fun m n => exists k, k + m = n.

Definition Even : nat -> Prop :=
  fun n => exists k, n = 2 * k.

(** Exercise 15.1

State and prove that 3 is not less than 1.

 *)

Lemma three_not_leq_one : ~ (leq 3 1).
Proof.
  exact fill_me.
Qed.

(** Exercise 15.2

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

(** Exercise 15.3

State and prove that for every Nat n, the successor of n is not less
than or equal to n.

*)

Lemma Sn_not_leq_n : forall n, ~ (leq (S n) n).
Proof.
  exact fill_me.
Qed.

(** Exercise 15.4

State and prove that 1 is not Even.

 *)

Lemma three_is_not_even : ~ (Even 1).
Proof.
  exact fill_me.
Qed.

(** Exercise 15.C1

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

(** Exercise 15.C2

Prove that the Principle of the Excluded Middle is equivalent to using double
negation to prove a proposition.

Hint:

To prove that double negation imples excluded middle you'll need to use the evidence
for the double negation of the exluded middle, [double_neg_pem].
 *)


Definition double_neg_pem : forall X, ~~ (X \/ ~ X) :=
  fun X pem_false => (pem_false (or_intror (fun x => (pem_false (or_introl x))))).

(** NB: This theorem can be proved with only a single quantifier. The converse is not
true with a single quantifier. It's still possible to prove that excluded middle and double
negation are equivalent but quantifiers on both sides of the implication are required ([double_neg_imples_pem]) *)
Theorem pem_X_imples_double_neg_X : forall X, (X \/ ~ X) -> ((~~ X) -> X).
Proof.
  exact fill_me.
Qed.

Theorem pem_imples_double_neg : (forall X, (X \/ ~ X)) -> (forall Y, ((~~ Y) -> Y)).
Proof.
  exact fill_me.
Qed.

Theorem double_neg_implies_pem : (forall X, ((~~ X) -> X)) -> (forall Y, (Y \/ ~ Y)).
Proof.
  exact fill_me.
Qed.
