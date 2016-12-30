Require Import Cpdt.CpdtTactics.
Require Import List.

Section plist.
  Variable A : Set.
  Variable P : A -> Prop.

  Inductive plist : nat -> Set :=
  | PNone : plist O
  | PSat : forall x, P x -> forall n, plist n -> plist (S n)
  | PCons : A -> forall n, plist n -> plist n.

  Definition count (n : nat) (l : plist n) := n.

  (* 'in' needed here *)
  Fixpoint pconcat n1 n2 (l1 : plist n1) (l2 : plist n2) : plist (n1 + n2) :=
    match l1 in plist n1 return plist (n1 + n2) with
    | PNone => l2
    | PSat x h n l => PSat x h (n + n2) (pconcat n n2 l l2)
    | PCons x n l => PCons x (n + n2) (pconcat n n2 l l2)
    end.

  Fixpoint plistOut n (l : plist n) :=
    match l with
    | PNone => nil
    | PSat x _ n l => x :: plistOut n l
    | PCons x n l => x :: plistOut n l
    end.

  Fixpoint countP {A : Type} {P Q : A -> Prop} (p : forall x : A, sumbool (P x) (Q x)) (l : list A) :=
    match l with
    | nil => O
    | cons x xs => if p x then S (countP p xs) else countP p xs
    end.


  Variable pdec : forall x, { P x } + { ~ P x }.

  Fixpoint plistIn (l : list A) :
    { n : nat & { pl : plist n | countP pdec l = n }}.
  induction l; simpl. Print existT.
  refine (existT (fun k : nat => {_ : plist k | O = k}) O _).
  Print sig. refine (exist _ PNone (eq_refl O)).
  destruct (pdec a). inversion IHl.
  refine (existT _ (S x) _).
  inversion H. Print exist. Print f_equal.
  refine (exist _ (PSat a p x x0) (f_equal S H0)).
  inversion IHl.
  refine (existT _ x _). apply H.
  Defined. Print plistIn.

End plist.