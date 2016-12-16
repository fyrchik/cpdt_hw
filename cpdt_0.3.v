Require Import Cpdt.CpdtTactics.

(* 1 *)
CoInductive itree (A : Type) : Type :=
| Node : A -> itree A -> itree A -> itree A.

CoFixpoint everywhere {A : Type} (x : A) : itree A :=
  Node A x (everywhere x) (everywhere x).

CoFixpoint map {A B C : Type} (f : A -> B -> C)
    (t1 : itree A) (t2 : itree B) :=
  match t1 with Node _ x l1 r1
  => match t2 with Node _ y l2 r2
      => Node _ (f x y) (map f l1 l2) (map f r1 r2)
     end
  end.

CoFixpoint falses := everywhere true.

CoFixpoint true_false : itree bool :=
  Node bool true
    (Node bool false true_false true_false)
    (Node bool false true_false true_false).

CoFixpoint true_false' : itree bool :=
  Node bool true false_true' false_true'
with false_true' : itree bool :=
  Node bool false true_false' true_false'.

CoInductive itree_eq {A : Type} : itree A -> itree A ->Prop :=
  | ITree_eq : forall x l1 l2 r1 r2, itree_eq l1 l2 -> itree_eq r1 r2 ->
      itree_eq (Node _ x l1 r1) (Node _ x l2 r2).

Definition useless {A : Type} (t : itree A) :=
  match t with
  | Node _ x l r => Node A x l r
  end.

Theorem useless_is_useful : forall {A : Type} (t : itree A), t = useless t.
Proof.
  intros; destruct t; reflexivity.
Qed.

Require Import Bool.

Theorem true_false_or : itree_eq true_false (map orb true_false falses).
Proof.
  cofix. rewrite (useless_is_useful true_false).
  rewrite (useless_is_useful (map _ _ _)). simpl.

Qed.