Require Import Vector Arith Bool List Nat.

(*
To prove 1 /= 6 you can use the discriminate tactic. But let's
port the code from Pie to construct the term without discriminate.

Lemma one_not_six : ~ 1 = 6.
  discriminate.
Defined.
*)

Fixpoint eq_consequence (n j : nat) : Prop.
  induction n.
  - induction j.
    + exact True.
    + exact False.
  - induction j.
    + exact False.
    + apply (eq_consequence n j).
Defined.

Lemma consequence_same : forall n, eq_consequence n n.
  intro n.
  induction n.
  - exact I.
  - exact IHn.
Defined.

Lemma use_Nat_eq : forall n j, n = j -> eq_consequence n j.
  intros.
  induction H.
  apply consequence_same.
Defined.

Lemma zero_not_add_one : forall n, ~ 0 = S n.
  unfold not.
  intros.
  exact (use_Nat_eq 0 (S n) H).
Defined.

Search (S _ = S _ -> _ = _).
(* eq_add_S: forall n m : nat, S n = S m -> n = m *)

Lemma one_not_six : ~ (1 = 6).
Proof.
  unfold not.
  intro.
  apply eq_add_S in H.
  exact (zero_not_add_one 4 H).
Defined.

Definition front' : forall E l, (Vector.t E (S l) -> forall k, (S l) = S k -> E).
  intros.
  induction X.
  - apply zero_not_add_one in H.
    induction H.
  - exact h.
Defined.

Definition front : forall E l, Vector.t E (S l) -> E.
  intros.
  exact ((front' E l X) l (eq_refl (S l))).
Defined.

Definition pem_is_not_false : forall X, ~~ (X \/ ~ X) :=
  fun X pem_false => (pem_false
                        (or_intror
                           (fun x => (pem_false (or_introl x))))).
