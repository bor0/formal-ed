Load "ed_defs.v".

Require Import String.
Require Import Coq.Init.Logic.
Require Import Coq.Lists.List.

Local Open Scope string_scope.

(*
A text editor is a computer program that lets a user insert, read, and change text.
We assume that strings can be inserted, read, and changed.
*)

(* Example and proof that we can insert any text *)
Definition example_buffer := fst (EditorEval (InsertLine 1 "a") nil).
Compute example_buffer.

Theorem can_insert_text :
  forall (s : string) (n : nat), exists (b : list string),
  fst (EditorEval (InsertLine n s) b) = s :: nil.
Proof.
  intros s n.
  simpl.
  unfold insertLine.
  exists nil. simpl.
  case n.
    - simpl. reflexivity.
    - intros. simpl. reflexivity.
Qed.

(* Example and proof that we can read any inserted text *)
Compute snd (EditorEval (ReadLine 0 "") example_buffer).

(* Example and proof that we can change any inserted text *)
Load "ed_lemmas.v".

Theorem can_read_text :
  forall (s : string) (n : nat) (b : list string),
  n <= List.length b
  ->
  snd (EditorEval (ReadLine n "") (fst (EditorEval (InsertLine n s) b))) = s.
Proof.
  intros s n b n_lt_buffer.
  simpl.
  unfold insertLine. unfold readLine.
  symmetry.
  assert (a := thm_1 n b (nil ++ skipn n b) s "").
  exact (a n_lt_buffer).
Qed.

Definition example_buffer_2 := fst (EditorEval (InsertLine 1 "b") (fst (EditorEval (InsertLine 1 "a") nil))).
Compute example_buffer_2.
Compute (fst (EditorEval (ReadLine 1 "") (fst (EditorEval (InsertLine 1 "c") (fst (EditorEval (DeleteLine 1 "") example_buffer_2)))))).
Compute (readLine example_buffer_2 1 "").
Compute (insertLine (deleteLine example_buffer_2 1) 1 "A").

Theorem can_change_text :
  forall (s1 s2 : string) (n : nat) (b : list string),
  n <= List.length b
  ->
  s1 = snd (EditorEval (ReadLine n "") b)
  ->
  s2 = (snd (EditorEval (ReadLine n "") (fst (EditorEval (InsertLine n s2) (fst (EditorEval (DeleteLine n "") b)))))).
Proof.
  intros s1 s2 n b n_lt_b. simpl. intros s1_smth.
  unfold readLine. unfold insertLine.
  simpl.
  assert (a := thm_1 n (deleteLine b n) (skipn n (deleteLine b n)) s2 "").

  case a.
    - unfold deleteLine. simpl.
      rewrite (app_length (firstn n b) (skipn (n + 1) b)).
      rewrite (lemma_1 b n n_lt_b).
      exact (Nat.le_add_r n (List.length (skipn (n + 1) b))).
   - reflexivity.
Qed.
