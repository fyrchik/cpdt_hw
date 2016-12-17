Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.

(* 1 *)
CoInductive itree (A : Type) : Type :=
| Node : A -> itree A -> itree A -> itree A.

CoFixpoint everywhere {A : Type} (x : A) : itree A :=
  Node x (everywhere x) (everywhere x).

CoFixpoint map {A B C : Type} (f : A -> B -> C)
    (t1 : itree A) (t2 : itree B) :=
  match (t1, t2) with
  | (Node x l1 r1, Node y l2 r2) =>
      Node (f x y) (map f l1 l2) (map f r1 r2)
  end.

CoFixpoint falses := everywhere false.
CoFixpoint trues := everywhere true.

CoFixpoint true_false : itree bool := let ft := Node false true_false true_false in
  Node true ft ft.

CoFixpoint true_false' : itree bool :=
  Node true false_true' false_true'
with false_true' : itree bool :=
  Node false true_false' true_false'.

CoInductive itree_eq {A : Type} : itree A -> itree A ->Prop :=
  | ITree_eq : forall x l1 l2 r1 r2, itree_eq l1 l2 -> itree_eq r1 r2 ->
      itree_eq (Node x l1 r1) (Node x l2 r2).

Definition u {A : Type} (t : itree A) :=
  match t with
  | Node x l r => Node x l r
  end.

Theorem uiu : forall {A : Type} (t : itree A), t = u t.
Proof.
  intros; destruct t; reflexivity.
Qed.

Definition value {A : Type} (t : itree A) : A :=
  match t with
  | Node x _ _ => x
  end.

Definition left {A : Type} (t : itree A) : itree A :=
  match t with
  | Node _ l _ => l
  end.

Definition right {A : Type} (t : itree A) : itree A :=
  match t with
  | Node _ _ r => r
  end.

Section itree_eq_coind.
  Variable A : Type.
  Variable R : itree A -> itree A -> Prop.

  Hypothesis Value_case : forall t1 t2, R t1 t2 -> value t1 = value t2.
  Hypothesis Left_case : forall t1 t2, R t1 t2 -> R (left t1) (left t2).
  Hypothesis Right_case : forall t1 t2, R t1 t2 -> R (right t1) (right t2).

  Theorem itree_eq_coind : forall t1 t2, R t1 t2 -> itree_eq t1 t2.
  Proof.
    cofix; destruct t1; destruct t2; intros.
    generalize (Value_case H); intro; simpl in H0; rewrite <- H0.
    constructor; apply itree_eq_coind; [ apply (Left_case H) | apply (Right_case H) ].
  Qed.
End itree_eq_coind.

Require Import Bool.
Check itree_eq_coind.

Theorem false_is_fixp : forall b, b || false = b.
Proof.
  destruct b; reflexivity.
Qed.

Hint Rewrite false_is_fixp.

Theorem falses_is_fixp : forall t, itree_eq t (map orb t (everywhere false)).
Proof.
  cofix; destruct t; rewrite (uiu (map _ _ _)); crush;
  constructor; apply falses_is_fixp.
Qed.

Theorem true_false_or : itree_eq true_false (map orb true_false (everywhere false)).
Proof.
  cofix; apply (falses_is_fixp true_false).
Qed.