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
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Definition leq a b := exists k, k + a = b.

Lemma one_leq_two : leq 1 2.
Proof.
  exists 1.
  ring.
Qed.

Lemma not_two_leq_one : ~leq 2 1.
Proof.
  unfold leq.
  unfold not.
  intros.
  destruct H.
  assert (one_plus_one_two : 2 = 1 + 1).
  ring.
  rewrite one_plus_one_two in H.
  assert (x_succ : forall x, x + (1 + 1) = S (S x)).
  intros.
  ring.
  rewrite x_succ in H.
  assert (contra : S x = O).
  apply (eq_add_S (S x) O H).
  discriminate.
Qed.
