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

  Fixpoint plistIn (l : list A) : plist (countP pdec l) :=
    match l return plist (countP pdec l) with
    | nil => PNone
    | x :: xs =>
        match pdec x as s
          return plist (if s then (S (countP pdec xs))
                            else (countP pdec xs)) with
        | left h => PSat x h _ (plistIn xs)
        | right _ => PCons x _ (plistIn xs)
        end
    end.

  Theorem in_out_inverse : forall l, plistOut _ (plistIn l) = l.
  Proof.
    induction l.
      reflexivity.
      simpl; destruct (pdec a); simpl;
        rewrite IHl; reflexivity.
  Qed.

  Fixpoint grab (n : nat) (ls : plist (S n)) : sig P :=
    match ls with
    | PNone => tt
    | PSat x h _ _ => exist _ x h
    | PCons x O xs => tt
    | PCons x (S len) xs => grab len xs
    end.

End plist.