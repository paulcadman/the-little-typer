Require Import Vector Arith Bool List Nat.

(** Exercises for Chapter 15 of The Little Typer *)

Definition leq : nat -> nat -> Prop :=
  fun m n => exists k, k + m = n.

Definition Even : nat -> Prop :=
  fun n => exists k, n = 2 * k.

(** Exercise 15.1

State and prove that 3 is not less than 1.

 *)

Lemma three_not_leq_one : ~ (leq 3 1).
Proof.
  unfold not.
  intros.
  destruct H.
  Search (S _ = S _ -> _ = _).
  Search (_ + 1 = S _).
  Search (?x + ?y = ?y + ?x).
  Search (S _ <> 0).
  (* Nat.neq_succ_0: forall n : nat, S n <> 0 *)
  (* Nat.add_comm: forall n m : nat, n + m = m + n *)
  (* Nat.add_1_r: forall n : nat, n + 1 = S n *)
  rewrite Nat.add_comm in H.
  apply eq_add_S in H.
  apply Nat.neq_succ_0 in H.
  exact H.
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
  unfold not.
  intros.
  induction n.
  - apply Nat.neq_0_succ in H.
    exact H.
  - apply eq_add_S in H.
    exact (IHn H).
Qed.

(** Exercise 15.3

State and prove that for every Nat n, the successor of n is not less
than or equal to n.

*)

Lemma Sn_not_leq_n : forall n, ~ (leq (S n) n).
Proof.
  unfold not.
  intros.
  induction n.
  - destruct H.
    Search (_ + 1 = S _).
    (* Nat.add_1_r: forall n : nat, n + 1 = S n *)
    rewrite Nat.add_1_r in H.
    apply Nat.neq_succ_0 in H.
    exact H.
  - destruct H.
    rewrite Nat.add_succ_r in H.
    apply eq_add_S in H.
    exact (IHn (ex_intro _ x H)).
Qed.

(** Exercise 15.4

State and prove that 1 is not Even.

 *)

Lemma one_is_not_even : ~ (Even 1).
Proof.
  unfold not.
  intros.
  destruct H.
  induction x.
  - apply Nat.neq_succ_0 in H.
    exact H.
  - Search (?x * (_ + _) = ?x * _ + ?x * _).
    (* Nat.mul_add_distr_l: *)
    (*   forall n m p : nat, n * (m + p) = n * m + n * p *)
    Search (1 + ?x = S ?x).
    Check Nat.add_1_r.
    Check Nat.add_1_l.
    (* Nat.add_1_l *)
    (*      : forall n : nat, 1 + n = S n *)
    rewrite <- (Nat.add_1_r x)  in H.
    rewrite (Nat.mul_add_distr_l 2 x 1) in H.
    Search (?x + ?y = ?y + ?x).
    rewrite Nat.add_comm in H.
    Search (_ * 1 = _).
    rewrite Nat.mul_1_r in H.
    apply eq_add_S in H.
    Search (0 <> S _).
    apply Nat.neq_0_succ in H.
    exact H.
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

Definition rest' : forall E l, (Vector.t E (S l) -> forall k, (S l) = S k -> Vector.t E k).
  intros.
  induction X.
  - apply Nat.neq_0_succ in H.
    induction H.
  - apply eq_add_S in H.
    rewrite H in X.
    exact X.
Defined.

Definition rest : forall E l, Vector.t E (S l) -> Vector.t E l.
  intros.
  exact ((rest' E l X) l (eq_refl (S l))).
Qed.

(** Exercise 15.C2

Prove that the Principle of the Excluded Middle is equivalent to using double
negation to prove a proposition.

Hint:

Have a look at the definition of [pem] in coq/ch15.v (relative to the root
of this repository). Though for these Theorems you'll probably want to use
tactics rather than an explicit lambda.
 *)


Definition double_neg_pem : forall X, ~~ (X \/ ~ X) :=
  fun X pem_false => (pem_false (or_intror (fun x => (pem_false (or_introl x))))).

Theorem pem_X_imples_double_neg_X : forall X, (X \/ ~ X) -> ((~~ X) -> X).
Proof.
  intros.
  unfold not in H.
  unfold not in H0.
  destruct H as [x | not_x].
  - exact x.
  - apply H0 in not_x.
    induction not_x.
Qed.

Theorem pem_imples_double_neg : (forall X, (X \/ ~ X)) -> (forall Y, ((~~ Y) -> Y)).
Proof.
  intros.
  apply (pem_X_imples_double_neg_X Y) in H.
  exact H.
  exact H0.
Qed.

Theorem double_neg_implies_pem : (forall X, ((~~ X) -> X)) -> (forall Y, (Y \/ ~ Y)).
Proof.
  intros.
  apply H.
  apply (double_neg_pem Y).
Qed.
