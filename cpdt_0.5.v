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

  Fixpoint plistIn (pdec : forall x, { P x } + { ~ P x }) (l : list A) :
    { n : nat & { pl : plist n | length (filter (fun e : A => if pdec e then true else false) l) = n }}.
  induction l; simpl. Check (existT (fun _ => ) O).

End plist.