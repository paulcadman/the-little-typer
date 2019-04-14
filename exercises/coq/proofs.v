Require Import Arith Bool List.

Theorem same_cons : forall A (e:A) (l1: list A) (l2: list A), l1 = l2 -> (e::l1) = (e::l2).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem same_lists :
  forall A (l1: list A) (l2: list A) (e1:A) (e2:A), e1 = e2 -> l1 = l2 -> (e1::l1) = (e2::l2).
  intros.
  rewrite H.
  apply (same_cons _ _ _ _ H0).
Qed.

Theorem same_lists2 :
  forall A (l1: list A) (l2: list A) (e1:A) (e2:A), e1 = e2 -> l1 = l2 -> (e1::l1) = (e2::l2).
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Theorem list_length_append_dist :
  forall A (l1:list A) (l2:list A), length (app l1 l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Definition leq a b := exists k, k + a = b.

Lemma one_leq_two : leq 1 2.
Proof.
  exists 1.
  ring.
Qed.

Search (_ -> False).

Search (?x + ?y = ?y + ?x).
Search (?x + 1 = S (?x)).
Search (?x + (?y + _) = (?x + ?y) + _).
Search (?x + (?y + _) = ?x + ?y + _).
(* Nat.add_1_r: forall n : nat, n + 1 = S n *)

Search (2 = _).
Print Nat.two_succ.

Lemma one_plus_one_two : 2 = 1 + 1.
Proof.
  simpl.
  reflexivity.
Defined.

Print one_plus_one_two.
Check eq_add_S.
(*eq_add_S
     : forall n m : nat, S n = S m -> n = m
*)
Locate "~".

Search (2 = 1 + 1).
Search (S O = 1 ).

Lemma not_two_leq_one : ~leq 2 1.
Proof.
  unfold leq.
  unfold not.
  intro H.
  destruct H as [k H1].
  rewrite BinInt.ZL0 in H1.
  rewrite Nat.add_assoc in H1.
  rewrite (Nat.add_1_r (k + 1)) in H1.
  apply  (eq_add_S (k+1) O) in H1.
  rewrite Nat.add_1_r in H1.
  discriminate.
Defined.