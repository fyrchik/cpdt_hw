Require Import CpdtTactics.

(** propositional logic *)

(* (10 minutes) Propositional logic often comes with an A <=> B form that is
true when A and B have the same truth values. Show how to define "iff" as
a Coq Prop. *)

Function iff (A : Prop) (B : Prop) : Prop := (A -> B) /\ (B -> A).

Notation "a <=> b" := (iff a b) (at level 77, right associativity).
Hint Unfold iff.

Theorem iff_refl : forall P : Prop, P <=> P.
Proof.
  auto.
Qed.

Theorem iff_sym : forall P Q : Prop, (P <=> Q) <=> (Q <=> P).
Proof.
  intros; constructor; intro; unfold iff in H; constructor; apply H.
Qed.

(* How automated can you make these proofs? *)

(* (15 minutes) In college-level logic classes, we learn that implication can
be expressed in terms of not and or operations (rather than in terms of
forall). *)
Definition implies (A B : Prop) : Prop := ~A \/ B.
Notation "a => b" := (implies a b) (at level 75, right associativity).
Hint Unfold implies.

(* One might wonder whether this form of implication is "the same as" Coq's
version that uses forall. State two theorems claiming that each kind of
implication can be converted into the other. Which one(s) can you prove? *)

Theorem impl_implies : forall A B : Prop, A -> B -> A => B.
Proof. (* auto *)
  intros; unfold implies; unfold not; right; assumption.
Qed.

Theorem implies_impl : forall A B : Prop, A => B -> A -> B.
Proof. 
  intros; unfold implies in H; inversion H.
    unfold not in H1; apply H1 in H0; contradiction.
    assumption.
Qed.

(* How about... *)
Axiom nowai : forall P : Prop, P \/ ~P.
(* ...now? *)

(* Some handy imports:
   Arith gives us nat, *, and +
   Arith.Even gives us even and odd
   Arith.Div2 gives us div2
*)
Require Import Arith.
Require Import Arith.Even.
Require Import Arith.Div2.
Set Implicit Arguments.
Hint Constructors even odd.

(** propositions with implicit equality *)

(* (35 minutes) The Collatz sequence starting at n is defined as the infinite
sequence obtained by iterating the step function:

step(n) = n/2  if n is even
step(n) = 3n+1 if n is odd

For example, the sequence starting at 11 looks like

11, 34, 17, 52, 26, 13, 40, 20, ...

It is conjectured that all collatz sequences eventually cycle (and in
particular reach 1 if they weren't 0 to begin with). Create an inductive
proposition collatz_cycles which expresses the fact that a particular nat
eventually reaches a cycle, then state and prove the fact that the collatz
sequence starting at 5 eventually cycles.

Don't forget about "Hint Constructors" and "auto n" when creating proofs about
constants!
*)
Print even.

(* sequence, starting with n reaches k *)
Inductive collatz_reaches : nat -> nat -> Prop :=
  | obv : forall k : nat, collatz_reaches k k
  | evC : forall k n : nat, even n -> collatz_reaches k (n / 2) ->
      collatz_reaches k n
  | odC : forall k n : nat, odd n -> collatz_reaches k (3 * n + 1) ->
      collatz_reaches k n.

Inductive collatz_cycles (n : nat) : Prop :=
  | Cev : (exists k, even k /\
      collatz_reaches k n /\ collatz_reaches k (k / 2)) -> collatz_cycles n
  | Cod : (exists k, odd k /\
      collatz_reaches k n /\ collatz_reaches k (3 * k + 1)) -> collatz_cycles n.

Hint Constructors collatz_reaches.

Theorem cc5 : collatz_cycles 5.
Proof.
  apply Cev; exists 4; split.
    auto 5. 
  split. apply odC; auto 6.
  simpl; apply evC; auto 17.
  simpl; apply evC; auto 9.
  simpl; apply evC; auto 5.
  simpl; apply odC; auto 2.
Qed.

(* (45 minutes) We say a list A is a "subsequence" of a list B when you can
produce list A by deleting some elements from list B.  For example, [1,2,3] is
a subsequence of each of the lists
[1,2,3]
[1,1,1,2,2,3]
[1,2,7,3]
[5,6,1,9,9,2,7,3,8]
but it is not a subsequence of any of the lists:
[1,2]
[1,3]
[5,6,2,1,7,3,8]

Define an inductive proposition subsequence that captures what it means to be
a subsequence, then prove that subsequence is transitive. Some hints on
automating this proof:

1. Use Hint Constructors to add your inductive proposition's constructors to
the hint database.
2. Choose which thing you do induction on carefully!
3. Try "crush" and look where it fails -- then add that as a lemma and put it
in your rewriting database. For example, on my first attempt, crush died here
first:

  A : Type
  l1 : list A
  H : subsequence l1 nil
  l : list A
  ============================
   subsequence l1 l

So I added a lemma:

Lemma subsequence_nil_anything : forall A (l1 l2 : list A),
    subsequence l1 nil -> subsequence l1 l2.
(* ... ;-) *)
Qed.

Hint Resolve subsequence_nil_anything.

That let crush get a bit farther, and suggested the next lemma I would need to
prove.
*)

Section subsequence.
  Variable T : Type.

(* 1st arg is subsequence of 2nd *)
Inductive subsequence : list T -> list T -> Prop :=
  | sNil : forall l, subsequence nil l
  | sTail : forall (b : T) (l l1 : list T), subsequence l l1 -> subsequence l (b :: l1)
  | sHead : forall (a b : T) (l l1 : list T), a = b -> subsequence l l1 -> subsequence (cons a l) (cons b l1).

Hint Constructors subsequence.

Hypothesis sub_nil_any : forall l, subsequence l nil -> forall l1, subsequence l l1.
Hypothesis sub_weak : forall a l l1, subsequence (a :: l) l1 -> subsequence l l1.
Hint Resolve sub_nil_any.

Theorem subsequence_trans : forall l l1, subsequence l l1 -> forall l2, subsequence l1 l2 ->
    subsequence l l2.
Proof.
  induction 2; crush. inversion H; crush. inversion H2; crush. inversion H; crush.

Qed.

(* I'm not really sure why we're not getting this notation for free, actually.
But we're not, se here it is for convenience. *)
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition sub123 := subsequence [1; 2; 3].
Definition notsub123 := fun l => ~(subsequence [1; 2; 3] l).
Hint Unfold sub123.

Example e1 : sub123 [1; 2; 3]. auto 100. Qed.
Example e2 : sub123 [1; 1; 1; 2; 2; 3]. auto 100. Qed.
Example e3 : sub123 [1; 2; 7; 3]. auto 100. Qed.
Example e4 : sub123 [5; 6; 1; 9; 9; 2; 7; 3; 8]. auto 100. Qed.
(* optional; you'll like inversion and unfold a lot
Example e5 : notsub123 [1; 2]. (* TODO *) Qed.
Example e6 : notsub123 [1; 3]. (* TODO *) Qed.
Example e7 : notsub123 [5; 6; 2; 1; 7; 3; 8]. (* TODO *) Qed.
*)
