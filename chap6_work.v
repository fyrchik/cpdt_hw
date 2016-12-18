Require Import List.

Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.

Inductive even : nat -> Prop :=
  | evenO : even O
  | evenS : forall n : nat, even n -> even (S (S n)).

Hint Constructors even.

Lemma EvenSS : forall n, even (S (S n)) -> even n.
Proof. 
  inversion 1; assumption.
Qed.

Lemma Even1 : even 1 -> False.
Proof.
  intro; inversion H.
Qed.

Fixpoint sum (a b : nat) {struct a} : even a -> even b -> { m : nat | even m } :=
  match a with
  | O => fun _ pb => exist even b pb
  | S O => fun p1 _ => False_rec _ (Even1 p1)
  | S (S n) => fun pa pb => sum (EvenSS pa) (evenS pb)
  end.

Lemma e6 : even 6. crush. Qed.
Lemma e4 : even 4. crush. Qed.

Eval compute in sum e4 e6.
Eval compute in proj1_sig (sum e4 e6).

Locate "{ _ } + { _ }".
Print sumbool.