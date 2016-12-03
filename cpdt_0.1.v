(** * CPDT Exercises 0.1 *)
(* 1 *)
Module Truth.

  Inductive truth : Set := Yes | No | Maybe.

  Function tnot (x : truth) : truth :=
    match x with
    | No => Yes
    | Yes => No
    | Maybe => Maybe
    end.

  Function tand (x : truth) (y : truth) : truth :=
    match x with
    | No => No
    | Yes => y
    | Maybe => match y with
               | No => No
               | _ => Maybe
               end
    end.

  (* because i want to be short *)
  Function tor (x : truth) (y : truth) : truth :=
    tnot (tand (tnot x) (tnot y)).

  Theorem tand_commute : forall x y : truth, tand x y = tand y x.
    destruct x; destruct y; reflexivity.
  Qed.

  (* because i can *)
  Theorem tor_commute : forall x y : truth, tor x y = tor y x.
    intros; unfold tor; rewrite <- tand_commute; reflexivity.
  Qed.

  Theorem tand_distributes : forall x y z : truth,
    tand x (tor y z) = tor (tand x y) (tand x z).

    destruct x; destruct y; destruct z; reflexivity.
  Qed.

End Truth.


(* 2 *)
Module SList.
  Require Import List.

  Section slist.
    Set Implicit Arguments.
    Variable T : Set.

    Inductive slist : Set :=
    | Empty : slist
    | Single : T -> slist
    | Concat : slist -> slist -> slist.

    Fixpoint flatten (s : slist) : list T :=
      match s with
      | Empty => nil
      | Single e => e :: nil
      | Concat l1 l2 => app (flatten l1) (flatten l2)
      end.

    Theorem flatten_distributes : forall s1 s2 : slist,
      flatten (Concat s1 s2) = app (flatten s1) (flatten s2).

      destruct s1; simpl; reflexivity.
    Qed.

  End slist.

  Implicit Arguments Empty [T].

End SList.


(* 5 *)
Module EvenOddNat.

  Inductive even : Set := OE | SE : odd -> even
    with odd  : Set := SO : even -> odd.

  (* We could do smth like this
     But proofs and formulae will be too long
     In exercise we need only sumEE, right? :)
  Fixpoint sumEE (e1 : even) (e2 : even) : even :=
    match e1 with
    | OE => e2
    | SE o => SE (sumOE o e2)
    end
  with sumOE (o1 : odd) (e2 : even) : odd :=
    match o1 with
    | SO e => SO (sumEE e e2)
    end.

  Fixpoint sumEO (e1 : even) (o2 : odd) : odd :=
    match e1 with
    | OE => o2
    | SE o => SO (sumOO o o2)
    end
  with sumOO (o1 : odd) (o2 : odd) : even :=
    match o1 with
    | SO e => SE (sumEO e o2)
    end.

  Scheme even_mut := Induction for even Sort Prop
     with odd_mut := Induction for  odd Sort Prop.
  *)

  (* But for this task it is interesting to write our own induction :)
     We can't do this trick with ODD though, because
     we will lack base of induction.
  *)

  Section even_ind'.
    Variable P : even -> Prop.

    Hypothesis OE_case : P OE.
    Hypothesis SE_case : forall e : even, P e -> P (SE (SO e)).

    Fixpoint even_ind' (e : even) : P e :=
      match e with
      | OE => OE_case
      | SE (SO e') => SE_case e' (even_ind' e')
      end.
  End even_ind'.

  Fixpoint sumEE (e1 : even) (e2 : even) : even :=
    match e1 with
    | OE => e2
    | SE (SO e) => SE (SO (sumEE e e2))
    end.

  Theorem sumEE_plus_OE :forall x : even, sumEE x OE = x.
      apply even_ind'.
        reflexivity.
        intros; simpl; rewrite -> H; reflexivity.
  Qed.

  (* probably too long *)
  Theorem sumEE_commute : forall x y : even, sumEE x y = sumEE y x.
Check even_ind'.
    apply (even_ind' (fun m => forall y : even, sumEE m y = sumEE y m)).
      intros; rewrite -> sumEE_plus_OE; reflexivity.
      intros; apply (even_ind' (fun m => sumEE _ m = sumEE m _)).
      simpl; rewrite -> sumEE_plus_OE; reflexivity.
      intros; simpl; rewrite -> H; rewrite <- H0; simpl; rewrite -> H; reflexivity.
  Qed.

  Function even2nat (e : even) : nat :=
    match e with
    | OE => O
    | SE o => S (odd2nat o)
    end
  with odd2nat (o : odd) : nat :=
    match o with
    | SO e => S (even2nat e)
    end.

  (* To prove another theorems we first must establish
     more useful induction scheme :)
  *)
End EvenOddNat.


(* 6 *)
Module NatTree.
  Require Import List.

  Inductive nat_tree :=
  | Leaf : nat -> nat_tree
  | Node : (nat -> nat_tree) -> nat_tree.

  Fixpoint increment (nt : nat_tree) : nat_tree :=
    match nt with
    | Leaf n => Leaf (S n)
    | Node f => Node (fun m => increment (f m))
    end.

  Fixpoint leapfrog (i : nat) (nt : nat_tree) : nat :=
    match nt with
    | Leaf n => n
    | Node f => leapfrog (S i) (f i)
    end.

  Theorem leapfrog_after_increment : forall (nt : nat_tree) (i : nat),
      leapfrog i (increment nt) = S (leapfrog i nt).
    induction nt.
      simpl; reflexivity.
      intros; simpl; rewrite -> H; reflexivity.
  Qed.

End NatTree.

(* 7 *)
Module TrExp.
  Require Import Arith.

  Section btree.
    Set Implicit Arguments.
    Variable T : Set.

    Inductive btree :=
    | BE : btree
    | BN : T -> btree -> btree -> btree.

    Check btree_rec.

    Function sumB (f : T -> nat) (b : btree) : nat :=
      match b with
      | BE => 0
      | BN x l r => f x + sumB f l + sumB f r
      end.

    Function everyB (f : T -> Prop) (b : btree) : Prop :=
      match b with
      | BE => True
      | BN x l r => f x /\ everyB f l /\ everyB f r
      end.

  End btree.

  Implicit Arguments BE [T].

  Inductive trexp : Set :=
  | L : nat -> trexp
  | N : btree trexp -> trexp.

  Section trexp_ind_mut.
    Variables
      (P : trexp -> Prop)
      (Q : btree trexp -> Prop).

    Hypotheses
      (L_case : forall n : nat, P (L n))
      (N_case : forall b : btree trexp, Q b -> P (N b))
      (BE_case : Q BE)
      (BN_case :
          forall x : trexp, P x ->
          forall l : btree trexp, Q l ->
          forall r : btree trexp, Q r ->
          Q (BN x l r)).

    Fixpoint trexp_ind_mut (tr : trexp) : P tr :=
      match tr with
      | L n => L_case n
      | N b => N_case ((fix bt_mut (b : btree trexp) : Q b :=
          match b with
          | BE => BE_case
          | BN x l r => BN_case (trexp_ind_mut x) (bt_mut l) (bt_mut r)
          end) b)
      end.

  End trexp_ind_mut.

  (* It is a bit LOL, but we must (or not?) define
     fix totalB inside, total because of Reflexive type.
     Then i define THE SAME totalB outside and proof that they
     are equal, so my mutual induction will work.
  *)
  Fixpoint total (te : trexp) : nat :=
    match te with
    | L n => n
    | N b => (fix totalB (tb : btree trexp) : nat :=
        match tb with
        | BE => 0
        | BN x l r => total x + totalB l + totalB r
        end) b
    end.

  Fixpoint increment (te : trexp) : trexp :=
    match te with
    | L n => L (S n)
    | N b => N ((fix incrB (tb : btree trexp) : btree trexp :=
        match tb with
        | BE => BE
        | BN x l r => BN (increment x) (incrB l) (incrB r)
        end) b)
    end.

  Fixpoint incrB (tb : btree trexp) : btree trexp :=
    match tb with
    | BE => BE
    | BN x l r => BN (increment x) (incrB l) (incrB r)
    end.

  Lemma incrB_as_fix : forall tb : btree trexp,
      incrB tb = ((fix incrB (tb : btree trexp) : btree trexp :=
        match tb with
        | BE => BE
        | BN x l r => BN (increment x) (incrB l) (incrB r)
        end) tb).
  Proof.
    induction tb. reflexivity.
    rewrite <- IHtb1; rewrite <- IHtb2;
    simpl; reflexivity.
  Qed.

  Fixpoint totalB (tb : btree trexp) : nat :=
    match tb with
    | BE => 0
    | BN x l r => total x + totalB l + totalB r
    end.

  Lemma totalB_as_fix : forall tb : btree trexp,
    totalB tb = (fix totalB (tb : btree trexp) : nat :=
        match tb with
        | BE => 0
        | BN x l r => total x + totalB l + totalB r
        end) tb.
  Proof.
    induction tb. reflexivity.
    rewrite <- IHtb1; rewrite <- IHtb2; reflexivity.
  Qed.

  Theorem total_incr : forall tr : trexp,
    total (increment tr) >= total tr.
  Proof. Check trexp_ind_mut.
    apply (trexp_ind_mut
      (fun s => total (increment s) >= total s)
      (fun m => totalB (incrB m) >= totalB m)).
    simpl; intros; apply le_S; apply le_n.
    simpl; intros; rewrite <- totalB_as_fix;
      rewrite <- incrB_as_fix; apply H.
    simpl; apply le_n.
    intros; simpl; apply plus_le_compat. apply plus_le_compat.
    apply H. apply H0. apply H1.
  Qed.
  
  (*
  http://cs.stackexchange.com/questions/104/recursive-definitions-over-an-inductive-type-with-nested-components
  without those 'useless' proofs of equality i was stuck
  *)

End TrExp.


(* 7 *)
Module NatBtree.
  Require Import Arith.

  Inductive nat_btree : Set :=
  | NLeaf : nat_btree
  | NNode : nat_btree -> nat -> nat_btree -> nat_btree.

  Fixpoint nnum (tr : nat_btree) : nat :=
    match tr with
    | NLeaf => O
    | NNode l n r => 1
    end.

  Fixpoint gnum (tr : nat_btree) : nat :=
    match tr with
    | NLeaf => O
    | NNode l n r => n
    end.

  Theorem leaf_ne_node : forall (n : nat) (l r : nat_btree),
      NLeaf <> NNode l n r.
  Proof.
    red; intros; change (eq_nat (nnum NLeaf) 1);
    rewrite -> H; reflexivity.
  Qed.

  Theorem eq_nodes_num : forall l1 r1 l2 r2 : nat_btree,
    forall n1 n2 : nat, NNode l1 n1 r1 = NNode l2 n2 r2 -> n1 = n2.
  Proof.
    intros; change (gnum (NNode l1 n1 r1) = gnum (NNode l2 n2 r2));
    rewrite -> H; reflexivity.
  Qed.
End NatBtree.