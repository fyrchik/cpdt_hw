(** * CPDT Exercises 0.2 *)
(* 1 *)
(*
  Prove these tautologies of propositional logic, using only the tactics apply, assumption,
  constructor, destruct, intro, intros, left, right, split, and unfold.
*)
Module ex1.
  Variable P Q R : Prop.

  Theorem p1 : (True \/ False) /\ (False \/ True).
  Proof.
    split; [ left; trivial | right; trivial].
  Qed.

  Theorem p2 : P -> ~ ~ P.
  Proof.
    unfold not; intros; apply H0; assumption.
  Qed.

  Theorem p3 : P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
  Proof.
    destruct 1; destruct H0;
      [ left; split; [ apply H | apply H0 ]
      | right; split; [ apply H | apply H0 ]
      ].
  Qed.

End ex1.

(*
  Prove the following tautology of first-order logic, using only the tactics apply, assert,
  assumption, destruct, eapply, eassumption, and exists. You will probably find the
  assert tactic useful for stating and proving an intermediate lemma, enabling a kind
  of “forward reasoning,” in contrast to the “backward reasoning” that is the default for
  Coq tactics. The tactic eassumption is a version of assumption that will do matching
  of unification variables. Let some variable T of type Set be the set of individuals. x
  is a constant symbol, p is a unary predicate symbol, q is a binary predicate symbol,
  and f is a unary function symbol
*)
Module ex2.
  Variable (T : Set) (x : T) (f : T -> T) (p : T -> Prop) (q : T -> T -> Prop).
  Theorem tt : p x
      -> (forall t, p t -> exists y, q t y)
      -> (forall t y, q t y -> q y (f y))
      -> (exists z, q z (f z)).
  Proof.
    
  Qed.
End ex2.

Module ex3.
  Require Import Arith Arith.Even Cpdt.CpdtTactics.

  Inductive mult_6_or_10 : nat -> Prop :=
    | m6 : forall n, mult_6_or_10 (n * 6)
    | m10: forall n, mult_6_or_10 (n * 10).

  Theorem not_satisfy_13 : ~ (mult_6_or_10 13).
  Proof.
    unfold not; inversion 1; crush.
  Qed.

  Hint Constructors even odd.
  Theorem satisfy_even : forall n, mult_6_or_10 n -> even n.
  Proof.
    inversion 1; apply even_mult_r; auto 11.
  Qed.
End ex3.