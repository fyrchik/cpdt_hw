(* Lecture 8, CIS 670, Fall 2012 *)

Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Introducing Subset Types *)

(* Note about the exercises:

For all of the versions of pred, to get some hands on practice,
try to implement a safe head function (for plain coq lists).

I've pointed out a few versions of pred which I think are good
to do this exercise on, but feel free to skip or add exercises
as you see fit. 

Some hints: if you want to do this for polymorphic lists (and why not?),
the type of the list elements should be in Set, not Type (try it).

Depending on how you set up the postcondition, you may need to add [eauto]
instead of just using [crush].
*)

(* Suppose we want to write a safe predecessor function. *)
Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

(* Exercise (Optional): Do the same for head. It should have type

head_strong1 (A : type) (l : list A) : (length l) > 0 -> nat
*)

Lemma egtz {A : Set} : length (nil : list A) > 0 -> False.
  crush.
Qed.

Definition head_strong1 (A : Set) (l : list A) : length l > 0 -> A :=
  match l with
  | nil => fun pf : length nil > 0 => match egtz pf with end
  | cons h t => fun _ => h
  end.

Theorem two_gt0 : 2 > 0.
  crush.
Qed.

Eval compute in pred_strong1 two_gt0.

(* We can do this with less ad-hoc types, using the [sig] type. *)
Print sig.

(* This type is similar to the existential type [ex], except that it
lives in [Set] instead of [Prop].

The main difference: we can project the witness out of a value of type
[sig], while we can't for a value of type [ex]. *)

(* Exercise (10 min.)
Write a function that takes a value of type sig, and returns
the witness value.

Try to write the same function for ex. What goes wrong?
*)

Print sig.
Definition myproj1_sig (A : Type) (P : A -> Prop) (s : sig P) : A :=
  match s with
  | exist x _ => x
  end.

Print ex.
(*
Definition myproj1_ex (A : Type) (P : A -> Prop) (s : ex P) : A :=
  match s with
  | ex_intro x _ => x
  end.

Error:
Incorrect elimination of "s" in the inductive type "ex":
the return type has sort "Type" while it should be "Prop".
Elimination of an inductive object of sort Prop
is not allowed on a predicate in sort Type
because proofs can be eliminated only to build proofs.
*)

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist O pf => match zgtz pf with end
    | exist (S n') _ => n'
  end.

Eval compute in pred_strong2 (exist _ 2 two_gt0).

(* We can guarantee the output is correct, as well *)

Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m} :=
  match s return {m : nat | proj1_sig s = S m} with
    | exist 0 pf => match zgtz pf with end
    | exist (S n') pf => exist _ n' (eq_refl _)
  end.

Eval compute in pred_strong3 (exist _ 2 two_gt0).

(* Exercise (Optional): Do the same thing for head. *)
Print ex.
Definition head_strong3 {A : Set} (s : {l : list A | length l > 0})
    : {h : A | ex (fun t => cons h t = proj1_sig s)} :=
  match s with
  | exist nil pf => match egtz pf with end
  | exist (cons h t) _ => exist _ h (ex_intro _ t (eq_refl (cons h t)))
  end.

(* We have managed to reach a type that is, in a formal sense, the most
expressive possible for [pred].  Any other implementation of the same
type must have the same input-output behavior.  However, there is
still room for improvement in making this kind of code easier to
write. Since we are explicitly passing around proofs in our functions,
it can get tedious to construct proof terms by hand everywhere.

A different approach: we write the skeleton of the function, then use
tactics to fill in the missing proofs. This uses the [refine] tactic,
which generates subgoals for missing proofs. *)

Definition pred_strong4 : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end); crush.
Defined.

(* Exercise: Do the same thing for head. *)

Definition head_strong4 {A : Set} : forall l : list A, length l > 0 ->
    {h : A | ex (fun t => cons h t = l)}.
  refine (fun l =>
    match l with
    | nil => fun _ => False_rec _ _
    | h :: t => fun _ => exist _ h _
    end
  ); crush; eauto.
Defined.
Print head_strong4. Extraction head_strong4.
(* We end the "proof" with [Defined] instead of [Qed]. Proofs marked
Qed can't be unfolded, while proofs marked with Defined can be. *)

Print pred_strong4.

Eval compute in pred_strong4 two_gt0.

(* Now, some syntax to make things more readable... *)

(* Read: Contradicted hypothesis. *)
Notation "!" := (False_rec _ _).

(* Read: Produced a value e, along with a proof that proposition
holds of e. *)
Notation "[ e ]" := (exist _ e _).

Definition pred_strong5 : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => !
      | S n' => fun _ => [n']
    end); crush.
Defined.

Eval compute in pred_strong5 two_gt0.

(* Exercise (30 min.)

Use this safe predecessor function to define a safe "minus 2" function,
with type

pred2_strong : forall (n : nat), n > 1 -> {m : nat | n = S (S m)}

*)
Search (_ > _ -> _ > _ -> _).
Require Import Arith.
Search (_ > O). Search (_ > _ -> _ > _). Check gt_S_n.
Definition pred2_strong : forall n, n > 1 -> {m : nat | n = S (S m)}.
  refine (fun n p =>
    match pred_strong5 (gt_trans n 1 O p (gt_Sn_O O)) with
    | exist n' e' =>
        match pred_strong5 (gt_S_n O n' _) with
        | exist n'' e'' => exist _ n'' _
        end
    end
  ); crush.
Defined.

Definition pred2_strong' : forall n : nat, n > 1 -> {m : nat | n = S (S m)}.
  refine (fun n =>
    match n with
    | O => fun _ => !
    | S O => fun _ => !
    | S (S n') => fun _ => [n']
    end
  ); crush.
Defined.

Extraction pred2_strong.
Extraction pred2_strong'.

(* Exercise (Optional)

Though defining functions that offer correctness guarantees is
requires a little more upfront work, they often compose better than
more weakly typed functions. For example, suppose we start with our
original predecessor function:

pred_strong1 : forall (n : nat), (n > 0) -> nat.

Try to use pred_strong1 to define a function

pred2_partial : forall (n : nat), (n > 1) -> nat.

*)

Hint Unfold pred_strong1.
Definition pred2_partial : forall n : nat, n > 1 -> nat. Print gt_trans.
  refine (fun n p =>
    pred_strong1 (_ : pred_strong1 (gt_trans n 1 O p (gt_Sn_O O)) > 0)
  ); unfold pred_strong1; destruct n; crush.


(*
  One other alternative is worth demonstrating.  Recent Coq versions
  include a facility called [Program] that
  streamlines this style of definition.  Here is a complete
  implementation using [Program].
*)

Obligation Tactic := crush.

Program Definition pred_strong6 (n : nat) (_ : n > 0) : {m : nat | n = S m} :=
  match n with
    | O => _
    | S n' => n'
  end.

Print pred_strong6.

(* [Program] and [refine] generate similar programs in this case.
In general, [refine] gives more control over the shape of the program. *)

Eval compute in pred_strong6 two_gt0.

(** * Detour: Decidable Proposition Types *)

(* There is another type in the standard library which captures the
idea of program values that indicate which of two propositions is
true. *)

Print sumbool.

(* Convention: the left constructor corresponds to success, while
the right constructor corresponds to failure. *)

(* Read: Found a witness of success, and a proof. *)
Notation "'Yes'" := (left _ _).

(* Read: Found a witness of failure, and a proof. *)
Notation "'No'" := (right _ _).

(* Read: If x succeeds, then take the proof of success and
convert to a proof of success for the entire expression.
Same if x fails. *)
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

(* Note that the [if] construct is overloaded: it works on a value of
any type with two constructors, returning either the first thing, or
the second thing. *)

(* A one example of [sumbool] is the decidable equality type,
which indicates that given two values, we can come up with a proof of
equality, or a proof of disequality. For instance, we can do this for
[nat]. *)

Definition eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
  refine (fix f (n m : nat) : {n = m} + {n <> m} :=
    match n, m with
      | O, O => Yes
      | S n', S m' => Reduce (f n' m')
      | _, _ => No
    end); congruence.
Defined.

(* Exercise (20 min.)

Write down the proof obligations that are generated by refine.
There's no need to write down every last hypothesis, just try to
write informally what is to be proved, under what hypothesis.
Try to do this without peeking.

For example, the first obligation should be:

Prove (0 = 0) under no hypothesis.
---
Prove (O <> S m') under no hypothesis
Prove (S n' <> O) under no hypothesis
Prove (S n' = S m') under hyp n' = m'
Prove (S n' <> S m') under hyp n' <> m'

*)

Eval compute in eq_nat_dec 2 2.

Eval compute in eq_nat_dec 2 3.

(* Exercise (Optional)

Write a decidable equality for lists of natural numbers.

*)
Print list_eq_dec.

Search ( _ -> _ :: _  = _ :: _).

Lemma eq_h_t : forall h1 h2 : nat, h1 = h2
    -> forall t1 t2 : list nat, t1 = t2 ->
    h1 :: t1 = h2 :: t2.
Proof.
  crush.
Qed.

Definition eq_list_nat_dec : forall l1 l2 : list nat, {l1 = l2} + {l1 <> l2}.
  induction l1, l2.
    auto 3.
    refine (right _); discriminate.
    refine (right _); discriminate.
    destruct (IHl1 l2), (eq_nat_dec a n).
      refine (left _); rewrite e, e0; reflexivity.
      refine (right _); crush.
      refine (right _); crush.
      refine (right _); crush.
Defined.
Print eq_list_nat_dec.

Lemma head_inj : forall (h1 h2 : nat) (t1 t2 : list nat), h1 :: t1 = h2 :: t2 -> h1 = h2.
crush. Qed.

Lemma tail_inj : forall (h1 h2 : nat) (t1 t2 : list nat), h1 :: t1 = h2 :: t2 -> t1 = t2.
crush. Qed.

Definition eq_list_nat_dec' : forall l1 l2 : list nat, {l1 = l2} + {l1 <> l2}.
  refine (fix f (l1 l2 : list nat) : {l1 = l2} + {l1 <> l2} :=
    match l1, l2 return {l1 = l2} + {l1 <> l2} with
    | nil, nil => left _ _
    | h1 :: t1, h2 :: t2 => match Reduce (eq_nat_dec h1 h2) with
        | left ph => match Reduce (f t1 t2) with
            | left p1 => left (eq_h_t ph p1)
            | right p2 => right (fun k => p2 (tail_inj k))
            end
        | right p3 => right (fun k => p3 (head_inj k))
        end
    | _, _ => No
    end
  ); crush.
Defined.

(* Or, we can use a tactic, [decide equality] *)
Definition eq_nat_dec' (n m : nat) : {n = m} + {n <> m}.
  decide equality.
Defined.

(* We can now write a list membership function which returns a proof
of membership, or a proof that the element is not in the list. *)

(* Read: if x returns a positive result, return a positive result.
Otherwise, evaluate y. *)
Notation "x || y" := (if x then Yes else Reduce y).

Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Definition In_dec : forall (x : A) (ls : list A), {In x ls} + {~ In x ls}.
    refine (fix f (x : A) (ls : list A) : {In x ls} + {~ In x ls} :=
      match ls with
	| nil => No
	| x' :: ls' => A_eq_dec x x' || f x ls'
      end); crush.
  Defined.
End In_dec.


Eval compute in In_dec eq_nat_dec 2 (1 :: 2 :: nil).


Eval compute in In_dec eq_nat_dec 3 (1 :: 2 :: nil).

(* Exercise (30 min.): Write a decidable equality function for
list A, assuming a decidable equality for A.

Hint: It might be good to start with some new notation...
*)

(** * Partial Subset Types *)

(* Up to this point, our types guarantee that on valid input, the output
of our function is correct. What if we want our functions to handle bad
input, say by producing a proof that the input is bad? *)

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

(** We can define some new notations, analogous to those we defined
for subset types. *)

(* Read: there is maybe an element x that satisfies P. *)
Notation "{{ x | P }}" := (maybe (fun x => P)).

(* Read: we failed to find an x, for some reason. *)
Notation "??" := (Unknown _).

(* Read: we found an x, and here is the proof that P x is
is satisfiable. *)
Notation "[| x |]" := (Found _ x _).

(** Now our next version of [pred] is trivial to write. *)

Definition pred_strong7 : forall n : nat, {{m | n = S m}}.
  refine (fun n =>
    match n return {{m | n = S m}} with
      | O => ??
      | S n' => [|n'|]
    end); trivial.
Defined.

(* Exercise (Optional): Do the same for head. *)

Eval compute in pred_strong7 2.

Eval compute in pred_strong7 0.

(* In the failure case, we don't provide any proof at all. The
implementation that always fails could be given this type. We
want to rule these out, and we'll use the [sumor] type, which
is either a value, or a proof. *)

Print sumor.

(* We add notations for easy use of the [sumor] constructors. *)

(* Read: here is a proof of B. (Convention: proof of failure) *)
Notation "!!" := (inright _ _).

(* Read: we found a witness x to the proposition P, and a proof that
P x. Note: only works when the "value" type in [sumor] is a subset
type. *)
Notation "[|| x ||]" := (inleft _ [x]).

(* Now, we can give a version of pred that works on all inputs,
and is fully specified. *)

Definition pred_strong8 : forall n : nat, {m : nat | n = S m} + {n = 0}.
  refine (fun n =>
    match n with
      | O => !!
      | S n' => [||n'||]
    end); trivial.
Defined.

Eval compute in pred_strong8 2.

Eval compute in pred_strong8 0.

(* Composing specified functions

Until now, we have been working with just the pred function. How
can we compose these functions together? Plumbing around all the
proofs is tedious, so we'll define some notation so we don't have
to deal with this. *)

(** * Monadic Notations *)

(** We can treat [maybe] like a monad, like how the Maybe type in
Haskell is interpreted as possible failure. *)

(* Read: If e1 produces a witness, see if e2 produces a witness.
If e1 fails, fail. *)
Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60).

(* Now, say we want to use [pred] to take the predecessor of two
values (at the same time!) *)

Definition doublePred : forall n1 n2 : nat, {{p | n1 = S (fst p) /\ n2 = S (snd p)}}.
  refine (fun n1 n2 =>
    m1 <- pred_strong7 n1;
    m2 <- pred_strong7 n2;
    [|(m1, m2)|]); tauto.
Defined.

(* Exercise (Optional): do the same for head. *)

(** We can build a [sumor] version of the "bind" notation and use it
to write a similarly straightforward version of this function. *)

(* Read: If e1 produces a proof of failure, produce a proof of failure.
If e1 produces a witness and a proof of success, evaulate e2. *)
Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

Definition doublePred' : forall n1 n2 : nat,
  {p : nat * nat | n1 = S (fst p) /\ n2 = S (snd p)}
  + {n1 = 0 \/ n2 = 0}.
  refine (fun n1 n2 =>
    m1 <-- pred_strong8 n1;
    m2 <-- pred_strong8 n2;
    [||(m1, m2)||]); tauto.
Defined.

(** * A Type-Checking Example *)

(* Let's use these ideas to build a certified typechecker. First,
our language... *)

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

Inductive type : Set := TNat | TBool.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
  hasType (Nat n) TNat
| HtPlus : forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool : forall b,
  hasType (Bool b) TBool
| HtAnd : forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.

(* We build a equality type decision procedure for [type]. *)

Definition eq_type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

(* In the process of generating the type, our typechecker will need
to assert that certain terms have specific types. We'll introduce
some notation to capture this pattern. *)

(* Read: If e1 succeeds (produces a witness), then do e2. Else, fail. *)
Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).

(* With the notation we've defined and some automation, we can create
a certified typechecker that is only a little more complex than the
uncertified typechecker. *)

Definition typeCheck : forall e : exp, {{t | hasType e t}}.
  Hint Constructors hasType.

  refine (fix F (e : exp) : {{t | hasType e t}} :=
    match e return {{t | hasType e t}} with
      | Nat _ => [|TNat|]
      | Plus e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TNat;; (* Assert that t1 is a nat *)
        eq_type_dec t2 TNat;; (* Assert that t2 is a nat *)
        [|TNat|]
      | Bool _ => [|TBool|]
      | And e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TBool;;
        eq_type_dec t2 TBool;;
        [|TBool|]
    end); crush.
Defined.

(** Despite manipulating proofs, our type checker is easy to run. *)

Eval simpl in typeCheck (Nat 0).

Eval simpl in typeCheck (Plus (Nat 1) (Nat 2)).

Eval simpl in typeCheck (Plus (Nat 1) (Bool false)).

(* The type checker also extracts to some reasonable OCaml code. *)

Extraction typeCheck.

(* We can adapt this implementation to use [sumor], so that we know
our type-checker only fails on ill-typed inputs.  First, we define an
analogue to the "assertion" notation. *)

(* Read: Same as e1 ;; e2, except if we fail this time, we get a proof
of failure, which we can return. *)
Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60).

(** Next, we prove a helpful lemma, which states that a given
expression can have at most one type. *)

Lemma hasType_det : forall e t1,
  hasType e t1
  -> forall t2, hasType e t2
    -> t1 = t2.
  induction 1; inversion 1; crush.
Qed.

(** Now we can define the type-checker.  Its type expresses that it
only fails on untypable expressions. *)

Definition typeCheck' : forall e : exp, {t : type | hasType e t} + {forall t, ~ hasType e t}.
  Hint Constructors hasType.
  (** We register all of the typing rules as hints. *)

  Hint Resolve hasType_det.
  (* Note that [hasType_det] has forall bound variables that don't
     show up in the final type, and so we need [eauto] to apply it. *)

  (** The implementation can be translated from our previous
      implementation, just by switching a few notations. *)

  refine (fix F (e : exp) : {t : type | hasType e t} + {forall t, ~ hasType e t} :=
    match e return {t : type | hasType e t} + {forall t, ~ hasType e t} with
      | Nat _ => [||TNat||]
      | Plus e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TNat;;;
        eq_type_dec t2 TNat;;;
        [||TNat||]
      | Bool _ => [||TBool||]
      | And e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TBool;;;
        eq_type_dec t2 TBool;;;
        [||TBool||]
    end); clear F; crush' tt hasType; eauto.

  (** We clear [F], the local name for the recursive function, to
  avoid strange proofs that refer to recursive calls that we never
  make. *)

  (* [crush'] is similar to [crush], except that it performs inversion
     on the types that we specify. We need [eauto] to apply [hasType_det]. *)
Defined.

(* Exercise (45 min.)

Add products to the language.

*)

(** The short implementation here hides just how time-saving
automation is.  Every use of one of the notations adds a proof
obligation, giving us 12 in total.  Most of these obligations require
multiple inversions and either uses of [hasType_det] or applications
of [hasType] rules.

Our new function remains easy to test, and now have additional
information in the failure case. *)

Eval simpl in typeCheck' (Nat 0).

Eval simpl in typeCheck' (Plus (Nat 1) (Nat 2)).

Eval simpl in typeCheck' (Plus (Nat 1) (Bool false)).
