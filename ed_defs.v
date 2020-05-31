Require Import Coq.Lists.List.

Inductive Command {X : Type} : Type :=
    | ReadLine : nat -> X -> Command
    | InsertLine : nat -> X -> Command
    | DeleteLine : nat -> X -> Command.

Definition readLine {X : Type} (buffer : list X) (pos : nat) (d : X) : X :=
  nth pos buffer d.

Definition insertLine {X : Type} (buffer : list X) (pos : nat) (s : X) : (list X) :=
  firstn pos buffer ++ s :: nil ++ skipn pos buffer.

Definition deleteLine {X : Type} (buffer : list X) (pos : nat) : (list X) :=
  firstn pos buffer ++ skipn (pos + 1) buffer.

Definition EditorEval {X : Type} (cmd : @Command X) (buffer : list X) : (list X * X) :=
  match cmd with
  | ReadLine   pos d => pair buffer (readLine buffer pos d)
  | InsertLine pos s => pair (insertLine buffer pos s) s
  | DeleteLine pos d => pair (deleteLine buffer pos) (readLine buffer pos d)
  end.
