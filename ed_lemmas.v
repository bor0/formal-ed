Require Import Coq.Lists.List.
Require Import PeanoNat.

Lemma lemma_1 : forall {X:Type} (l : list X) (n : nat),
  n <= length l
  ->
  length (firstn n l) = n.
Proof.
  exact firstn_length_le.
Qed.

Lemma lemma_2 : forall n m,
  n = m
  ->
  n >= m.
Proof.
  intros n m H.
  induction H.
  constructor.
Qed.

Lemma lemma_3 : forall {X:Type} n l1 l2 (s:X) d,
  length l1 = n
  ->
  s = nth n (l1 ++ s :: l2) d.
Proof.
  intros X n l1 l2 s d length_l1_eq_n.
  assert (n_eq_length_l1_to_gte_l1 := (lemma_2 n (length l1))).
  assert (n_gte_l1 := n_eq_length_l1_to_gte_l1 (eq_sym length_l1_eq_n)).
  rewrite (app_nth2 l1 (s::l2) d n_gte_l1).
  rewrite length_l1_eq_n.
  rewrite (Nat.sub_diag n).
  reflexivity.
Qed.

Theorem thm_1 : forall {X:Type} (n : nat) (l1 l2 : list X) (s : X) (d : X),
  n <= length l1
  ->
  s = nth n (firstn n l1 ++ s :: l2) d.
Proof.
  intros x n l1 l2 s d n_lt_length_l.
  apply lemma_3. exact (lemma_1 l1 n n_lt_length_l).
Qed.
