(* DPLL *)

Require Import Arith List Nat.
Require Import Cpdt.CpdtTactics.
Set Implicit Arguments.

Definition var  : Type := nat.

(*
  (b, true)  means  b
  (b, false) means ~b
*)
Definition occur : Type := var * bool.
Definition negVar : occur -> occur :=
    fun o => match o with (v, b) => (v, negb b) end.

Definition tVals : Type := var -> bool.
Definition evalOcc (t : tVals) (o : occur) : bool :=
  let (v,n) := o in (if n then negb (t v) else t v).

Definition setVar (t : tVals) (v : var) (b : bool) : tVals :=
  (fun n => if beq_nat v n then b else t n).

Definition TClause  : Type := list occur.
Definition TFormula : Type := list TClause.

Definition isEmpty (A : Type) (l : list A) : Prop :=
  match l with
  | nil => True
  | _ => False
  end.

(* empty clause means false *)
(* clause with unset values can still be true if it contains 
   variable which is set and is true
 *)
Fixpoint evalClause (t : tVals) (c : TClause) : bool :=
  match c with
  | nil => false
  | o :: rest => orb (evalOcc t o) (evalClause t rest)
  end.

Eval compute in evalClause (fun _ => true) nil = false.
Eval compute in evalClause (fun _ => true) ((1, true) :: nil) = false.
Eval compute in evalClause (fun _ => true) ((1, false) :: nil) = true.

(* remove falses *)
Definition simplClause (t : tVals) : TClause -> TClause :=
  filter (evalOcc t).

Lemma simplClause_correct : forall t c,
    evalClause t (simplClause t c) = evalClause t c.
Proof.
  induction c.
    reflexivity.
    destruct a as (v,b); destruct b; destruct (t v) eqn:tv; crush.
Qed.

(* empty formula means true *)
Fixpoint evalFormula (t : tVals) (f : TFormula) : bool :=
  match f with
  | nil => true
  | c :: rest => andb (evalClause t c) (evalFormula t rest)
  end.

Definition simplify (t : tVals) (f : TFormula) : TFormula :=
  filter (fun c => negb (evalClause t c)) (map (simplClause t) f).

Lemma simplify_correct : forall t f,
    evalFormula t (simplify t f) = evalFormula t f.
Proof.
  induction f.
    reflexivity. 
    unfold simplify. simpl. rewrite simplClause_correct.
    destruct (evalClause t a) eqn:eta.
      simpl; assumption.
      simpl; rewrite simplClause_correct; rewrite eta; reflexivity.
Qed.

Definition formulaTrue (t : tVals) (f : TFormula) := evalFormula t f = true.

Lemma simplify_SAT : forall f t v, let sv := setVar t v in
      formulaTrue (sv true) (simplify (sv true) f)
      \/ formulaTrue (sv false) (simplify (sv false) f) ->
      ex (fun tr => formulaTrue tr f).
Proof.
  unfold formulaTrue; intros; destruct H; rewrite simplify_correct in H;
    [ exists (setVar t v true) | exists (setVar t v false) ];
    assumption.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma set_same : forall t v, (setVar t v (t v)) = t.
Proof.
  crush. apply functional_extensionality.
  intro k.
   unfold setVar; destruct (beq_nat v k) eqn:e.
    apply beq_nat_true in e; rewrite e; reflexivity.
    reflexivity.
Qed.

Lemma simplify_UNSAT : forall f v, (forall t, let sv := setVar t v in
  ~ formulaTrue (sv true) (simplify (sv true) f) /\
  ~ formulaTrue (sv false) (simplify (sv false) f)) ->
  forall tr, ~ formulaTrue tr f.
Proof.
  unfold formulaTrue. induction f.
    crush.
    intros v H tr. remember (H tr) as Htr. clear HeqHtr H.
      destruct Htr as [Ht Hf]. rewrite simplify_correct in Ht, Hf.
      destruct (tr v) eqn:trv.
      rewrite <- trv in Ht at 1; rewrite set_same in Ht; assumption.
      rewrite <- trv in Hf at 1; rewrite set_same in Hf; assumption.
Qed.

Definition dpllAux : forall (t : tVals) (f : TFormula), nat ->
  option (
    {truth : tVals | formulaTrue truth f } +
    {forall truth, ~ formulaTrue truth f }
  ).
  refine (fix dpll t f bound :=
    match bound with
    | O => None
    | S n' =>
        match f return option (
    {truth : tVals | formulaTrue truth f } +
    {forall truth, ~ formulaTrue truth f }
  ) with
        | nil => Some (inleft _)
        | c :: fr =>
            match c with
            | nil => Some (inright _ _)
            | (v,n) :: cr =>
                let sv := setVar t v in
                let r1 := dpll (sv true) (simplify (sv true) f) n' in
                  match r1 with
                  | Some (inleft _) => Some (inleft _)
                  | _ => let r2 := dpll (sv false) (simplify (sv false) f) n' in
                      match r2 with
                      | Some (inleft _) => Some (inleft _)
                      | Some (inright _) => Some (inright _)
                      | _ => None
                      end
                  end
            end
        end
    end).

Hint Unfold formulaTrue.
    exists t; crush.
    unfold not; intros; unfold formulaTrue in H; simpl in H.
    inversion H.
Print sig.