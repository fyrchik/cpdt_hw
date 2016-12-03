(* CIS670, Homework 4 *)

(* Try to do this assignment "from memory" as much as possible,
    without peeking at CPDT.  If you need a hint, reread the
    appropriate sections in CPDT without touching the keyboard, then
    close the book and try again. *)

Module BinaryTrees.

Inductive binary : Set :=
| leaf : nat -> binary
| node : (binary * binary) -> binary.

Check binary_ind.

Section binary_ind'.
  Variable P : binary -> Prop.

  Hypothesis Leaf_case : forall n : nat, P (leaf n).
  Hypothesis Node_case : forall (l r : binary), P l -> P r -> P (node (l, r)).

  Fixpoint binary_ind' (b : binary) : P b :=
    match b with
    | leaf n => Leaf_case n
    | node (l, r) => Node_case l r (binary_ind' l) (binary_ind' r)
    end.

End binary_ind'.

Fixpoint cbi
           (P : binary -> Prop)
           (cl : forall n : nat, P (leaf n))
           (cn : forall l r : binary, P l -> P r -> P (node (l, r)))
           (b : binary) :=
  match b return (P b) with
    | leaf n => cl n
    | node (l, r) => cn l r (cbi P cl cn l) (cbi P cl cn r)
  end.

(* TODO: 
  - write down the type of the induction principle that Coq will
    generate for [binary] (without asking Coq for help)
  - use Coq to check your answer
  - write down the type of the _most natural / useful_ induction
    principle for [binary]
  - construct a term that has this type 
*)

End BinaryTrees.


(* *************************************************************** *)

Module InfiniteBranchingTrees.

Inductive tree : Set :=
| leaf : tree
| node : (nat -> tree) -> tree.

Section tree_ind'.
  Variable P : tree -> Prop.

  Hypothesis Leaf_case : P leaf.
  Hypothesis Node_case : forall t : nat -> tree,
                           (forall n : nat, P (t n)) -> P (node t).

  Fixpoint tree_ind' (x : tree) : P x :=
    match x with
      | leaf => Leaf_case
      | node f => Node_case f (fun n : nat => tree_ind' (f n))
    end.
End tree_ind'.

Check tree_ind'.

(* TODO: 
  - Build a suitable induction principle (by hand) *)

End InfiniteBranchingTrees.


(* *************************************************************** *)
Module RB.

(* Here is a simple datatype declaration describing one of the key
   structural properties of red-black trees -- the fact that both
   children of a red node must be black. *)

Inductive node : Set := 
| R : red -> node
| B : black -> node

with red : Set :=
| RN : nat -> black -> black -> red

with black : Set := 
| BL : black
| BN : nat -> node -> node -> black.

Scheme node_ind' := Induction for node Sort Prop
with red_ind' := Induction for red Sort Prop
with black_ind' := Induction for black Sort Prop.

Check node_ind'.

Section node_ind''.
  Variable Pn : node -> Prop.
  Variable Pb : black -> Prop.
  Variable Pr : red -> Prop.

  Hypothesis node_R : forall r : red, Pr r -> Pn (R r).
  Hypothesis node_B : forall b : black, Pb b -> Pn (B b).

  Hypothesis red_RN : forall (n : nat) (b1 : black), Pb b1 ->
                        forall b2 : black, Pb b2 ->
                        Pr (RN n b1 b2).

  Hypothesis black_BL : Pb BL.
  Hypothesis black_BN : forall (n : nat) (n1 : node), Pn n1 ->
                          forall n2 : node, Pn n2 ->
                          Pb (BN n n1 n2).

  Fixpoint node_ind'' (x : node) :=
    match x return (Pn x) with
      | R r => node_R r (red_ind'' r)
      | B b => node_B b (black_ind'' b)
    end
  with red_ind'' (r : red) :=
    match r return (Pr r) with
      | RN n b1 b2 => red_RN n b1 (black_ind'' b1) b2 (black_ind'' b2)
    end
  with black_ind'' (b : black) :=
    match b return (Pb b) with
      | BL => black_BL
      | BN n n1 n2 => black_BN n n1 (node_ind'' n1) n2 (node_ind'' n2)
    end.

End node_ind''.

Print node_ind'.
Check node_ind''.

(* TODO: 
  - write down the type of the _most natural / useful_ induction
    principle for [node]
  - use [Scheme] to construct a term that has this type
  - construct another term of this type without using [Scheme]
*)

End RB.