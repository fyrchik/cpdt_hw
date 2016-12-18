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

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

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

