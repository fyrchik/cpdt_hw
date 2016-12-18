Require Import Cpdt.CpdtTactics.
Require Import Arith.

Set Implicit Arguments.

(* 1 *)
(* 1.1 Explicit definition *)
Fixpoint le_nat_dec (n m : nat) : { n <= m } + { n > m } :=
  match n with
  | O => left (le_O_n m)
  | S n' => match m with
      | O => right (gt_Sn_O n')
      | S m' => match le_nat_dec n' m' with
          | left p => left (le_n_S n' m' p)
          | right p => right (gt_n_S n' m' p)
          end
      end
  end.
Check le_nat_dec.
Extraction le_nat_dec.
(*
Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50, only parsing).

(* 1.2 Definition using refine *)
Definition le_nat_dec' : forall n m : nat, { n <= m } + { n > m }.
  refine (fix f n m :=
    match n with
    | O => Yes
    | S n' => match m with
        | O => No
        | S m' => Reduce (f n' m')
        end
    end
  ); crush.
Defined.
Check le_nat_dec'.
Extraction le_nat_dec.
*)
(* 2 *)
Require Import Bool.

Definition var := nat.

Inductive prop : Type :=
  | Var : var -> prop
  | Neg : prop -> prop
  | Conj : prop -> prop -> prop
  | Disj : prop -> prop -> prop.

Definition truthVar := var -> bool.

Fixpoint propDenote (t : truthVar) (p : prop) {struct p} : Prop :=
  match p with
  | Var v => if t v then True else False
  | Neg p => ~ propDenote t p
  | Conj a b => propDenote t a /\ propDenote t b
  | Disj a b => propDenote t a \/ propDenote t b
  end.
Print left.

(* semi-implicit construction *)
Definition bool_true_dec : forall b : bool, {b = true} + {b = true -> False}.
  refine (fix f b := match b with
    | true => left _ _
    | false => right _ _
    end
  ); crush.
Defined.

(* explicit construction *)
Definition bool_true_dec' (b : bool) : {b = true} + {b = true -> False} :=
  match b with
  | true => left (eq_refl true)
  | false => right (fun H => diff_false_true H)
  end.
Print left.

(* CRUCIAL thing for automation with crush *)
Hint Unfold not. (* Most important line *)
(* Do not delete previous line *)

(* TACTICAL construction *)
Definition decide : forall truth pr, {propDenote truth pr} + {~ propDenote truth pr}.
  intros. induction pr.
  simpl; destruct (truth v); crush.
  simpl; destruct IHpr; crush.
  simpl; destruct IHpr1, IHpr2; crush.
  simpl; destruct IHpr1, IHpr2; crush.
Defined.

(* REFINE construction (tried to make more explicit than i possibly should) *)
Definition decide' : forall truth pr, {propDenote truth pr} + {~ propDenote truth pr}.
  refine (fix d t p {struct p} :=
    match p return {propDenote t p} + {~ propDenote t p} with
    | Var v => match bool_true_dec (t v) with
        | left e => left _
        | right e => right _
        end
    | Neg b => match d t b with
        | left e => right _
        | right e => left _
        end
    | Conj a b => match (d t a, d t b) with
        | (left pa, left pb) => left (conj pa pb)
        | (_, _) => right _
        end
    | Disj a b => match (d t a, d t b) with
        | (left pa, _) => left (or_introl pa)
        | (_, left pb) => left (or_intror pb)
        | (right _, right _) => right _
        end
    end
  ); crush; destruct (t v); crush. (* destruct for 'right' case of 'Var' *)
Defined.

Definition negate : forall p : prop,
    { p' : prop | forall truth, propDenote truth p <-> ~ propDenote truth p' }.
Print sig.
  refine (fix n p :=
    match p with
    | Var v => exist _ (Neg (Var v)) _
    | Neg p => exist _ p _
    | Conj a b => exist _ (Disj (proj1_sig (n a)) (proj1_sig (n b))) _
    | Disj a b => exist _ (Conj (proj1_sig (n a)) (proj1_sig (n b))) _
    end
  ).
    intro t; crush; destruct (t v); crush.
    intro t; crush; simpl.
    destruct (n a), (n b); crush. 
      apply i in H1; assumption.
      apply i0 in H2; assumption.
    destruct (n a), (n b); crush.
      apply i in H0; assumption.
      apply i0 in H0; assumption.
    destruct (decide truth x), (decide truth x0); crush.
Defined.

Eval compute in proj1_sig (negate (Conj (Neg (Var 1)) (Neg (Var 2)))).