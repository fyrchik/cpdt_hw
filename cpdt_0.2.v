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
(* 1) if edestruct was permitted: *)
(*    edestruct 2; [ eassumption | exists x0; apply H2 in H1; assumption ]. *)

(* 2) apply with manually constructed proof is also a solution *)
    apply (
      fun (a : p x)
          (b : forall t, p t -> exists y, q t y)
          (c : forall t y, q t y -> q y (f y)) =>
        match b x a with
        | ex_intro _ k l => ex_intro (fun z => q z (f z)) k (c x k l)
        end
    ).
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

Module ex4.
  Require Import Arith.

  Definition var := nat.

  Inductive exp : Set :=
    | eConst : nat -> exp
    | eAdd : nat -> nat -> exp
    | ePair : exp -> exp -> exp
    | eFst : exp -> exp
    | eSnd : exp -> exp
    | eVar : var -> exp.

  Inductive cmd :=
    | cExp : exp -> cmd
    | cAss : var -> exp -> cmd -> cmd.

  Definition map (T : Type) := var -> T.

  Inductive value :=
    | ConstValue : nat -> value
    | PairValue : value -> value -> value.

  Inductive assignType :=
    | Env : map value -> assignType.

  Inductive eval : exp -> assignType -> value -> Prop :=
    | evV : forall n t, eval (eConst n) t (ConstValue n)
    | evA : forall n1 n2 t, eval (eAdd n1 n2) t (ConstValue (n1 + n2))
    | evP : forall e1 e2 t v1 v2,
        eval e1 t v1 -> eval e1 t v2 -> eval (ePair e1 e2) t (PairValue v1 v2)
    | evF : forall e1 e2 t v, eval e1 t v -> eval (ePair e1 e2) t v
    | evS : forall e1 e2 t v, eval e2 t v -> eval (ePair e1 e2) t v
    | evR : forall va (f : map value) v, f va = v -> eval (eVar va) (Env f) v.

  Section example.
    Variable a : assignType.
    Example e : eval (eAdd 1 1) a (ConstValue 2). apply evA. Qed.
  End example.

  Inductive run : cmd -> assignType -> value -> Prop :=
    | ruE : forall e v t, eval e t v -> run (cExp e) t v
    | ruV : forall vV vE c eV cV f,
        eval vE (Env f) eV ->
        run c (Env (fun n => if eq_nat_dec n vV then eV else f n)) cV ->
        run (cAss vV vE c) (Env f) cV.

  Inductive typeType :=
    | ConstType : typeType
    | PairType : typeType -> typeType -> typeType.

  Inductive typingType :=
    | Typing : map typeType -> typingType.

  Inductive isTypeOfExp : typingType -> typeType -> exp -> Prop :=
    | isConst : forall t n, isTypeOfExp t ConstType (eConst n)
    | isAdd : forall t n1 n2, isTypeOfExp t ConstType (eAdd n1 n2)
    | isPair : forall t e1 t1, isTypeOfExp t t1 e1 -> forall e2 t2, isTypeOfExp t t2 e2 ->
        isTypeOfExp t (PairType t1 t2) (ePair e1 e2)
    | isFst : forall t e1 t1, isTypeOfExp t t1 e1 -> forall e2, isTypeOfExp t t1 (eFst (ePair e1 e2))
    | isSnd : forall t e2 t2, isTypeOfExp t t2 e2 -> forall e1, isTypeOfExp t t2 (eSnd (ePair e1 e2))
    | isVar : forall f v, isTypeOfExp (Typing f) (f v) (eVar v).

  Inductive isTypeOfValue : typeType -> value -> Prop :=
    | isC : forall n, isTypeOfValue ConstType (ConstValue n)
    | isP : forall v1 t1, isTypeOfValue t1 v1 -> forall v2 t2, isTypeOfValue t2 v2 ->
        isTypeOfValue (PairType t1 t2) (PairValue v1 v2).

  Inductive isTypeOfCmd : typingType -> typeType -> cmd -> Prop :=
    | isExp : forall t t1 e, isTypeOfExp t t1 e -> isTypeOfCmd t t1 (cExp e)
    | isAss : forall f t1 e, isTypeOfExp (Typing f) t1 e ->
        forall v c tc, isTypeOfCmd (Typing (fun m => if eq_nat_dec v m then t1 else f m)) tc c ->
        isTypeOfCmd (Typing f) tc (cAss v e c).

  Inductive varsType : assignType -> typingType -> Prop :=
    | vtp : forall var fm tm v, fm var = v -> forall t, isTypeOfValue t v -> tm var = t ->
        varsType (Env fm) (Typing tm).

  Require Import Cpdt.CpdtTactics.

End ex4.
