(** * Coinduction: Infinite Data and Proofs *)
(* CIS670, Homework assignments 6 and 7 *)

(* This material builds on:
   - sections 7.1 from the tutorial by Giménez and Castéran
   - sections 5.1-5.2 from the CPDT book by Adam Chlipala
*)

Require Import Bool.
Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.

(* ------------------------------------------------------------ *)
(** ** Computing with Infinite Data *)

(** The most basic type of infinite data is infinite lists, usually
    known as _streams_ *)

CoInductive stream (A : Type) : Type :=
  | Cons : A -> stream A -> stream A.

(** If we want _both_ finite and infinite lists, then we can also keep
    the cons *)

CoInductive llist (A: Type) : Type :=
|  LNil : llist A
|  LCons : A -> llist A -> llist A.

(** Exercise (easy): define the coinductive types representing the
    following 3 infinite data structures: *)

(* 1. infinite binary trees *)
CoInductive ibtree (A : Type) : Type :=
  | IBNode : A -> ibtree A -> ibtree A -> ibtree A.

(* 2. infinitely branching infinite trees
      (i.e. infinitely wide and infinitely deep) *)
CoInductive itree (A : Type) : Type :=
  | INode : A -> (nat -> itree A) -> itree A.

(* 3. finitely and infinitely branching infinite trees
      (i.e. finitely or infinitely wide and infinitely deep *)
CoInductive iftree (A : Type) : Type :=
  | IINode : A -> llist (iftree A) -> iftree A.

(** Pattern matching on coinductive values works as usual *)

Definition head (A:Type) (s : stream A) :=
  match s with
  | Cons a s' => a
  end.

Definition tail (A : Type)(s : stream A) :=
  match s with
  | Cons a s' => s'
  end.

(* Exercise (easy): Using the functions head and tail, define a
   recursive function which takes the n-th element of an infinite
   stream. *)
Fixpoint nth (A : Type) (n : nat) (s : stream A) : A :=
  match n with
  | O => head s
  | S n' => nth n' (tail s)
  end.

(* Infinite objects are defined using the CoFixpoint command *)

CoFixpoint repeat (A : Type) (a : A) : stream A := Cons a (repeat a).

(** Note: whereas recursive definitions (fixpoints) were necessary to
    _use_ values of recursive inductive types effectively, we need
    co-recursive definitions (co-fixpoints) to _build_ (infinite)
    values of co-inductive types *)

(** Every CoFixpoint has to return a coinductive type (in the same way
    every Fixpoint has to take and break up an inductive argument). *)

(*
CoFixpoint to_bool (x : stream nat) : bool := to_bool x.

Error:
Recursive definition of to_bool is ill-formed.
In environment
to_bool : stream nat -> bool
x : stream nat
The codomain is "bool"
which should be a coinductive type.
Recursive definition is: "fun x : stream nat => to_bool x".
*)

(** Co-inductive values can be arguments to recursive functions.
    However, there also needs to be an inductive argument in order to
    convince Coq that the function is terminating. We can use this to
    write a function that computes the finite approximation of a
    stream: *)

Fixpoint approx A (n : nat) (s : stream A) {struct n} : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: approx n' t
      end
  end.

Definition ones := repeat 1.

Eval simpl in approx 10 ones.

(** We can of course also define [ones] directly, without using
    [iterate] *)

CoFixpoint ones' : stream nat := Cons 1 ones'.

Eval simpl in approx 10 ones'.

(** In order to prevent non-termination, co-fixpoints are evaluated
    lazily. They are unfolded _only_ when they appear as the argument
    of a match expression. We can check this using Eval. *)

Eval simpl in (repeat 4).

Eval simpl in (head (repeat 4)).

(** Here are three useful co-recursive functions on streams: *)

CoFixpoint iterate (A : Type) (f : A -> A) (a : A) : stream A :=
  Cons a (iterate f (f a)).

CoFixpoint map (A B : Type) (f : A -> B) (s : stream A) : stream B :=
  match s with
  | Cons a tl => Cons (f a) (map f tl)
  end.

CoFixpoint interleave (A : Type) (s1 s2 : stream A) : stream A :=
  match s1, s2 with
  | Cons n1 s1', Cons n2 s2' => Cons n1 (Cons n2 (interleave s1' s2'))
  end.

(** Using [iterate] we can define the stream of natural numbers: *)

Definition nats : stream nat := iterate S 0.
Eval simpl in approx 10 nats.

(* We can of course also define nats more directly: *)
CoFixpoint nats_from_n (n : nat) : stream nat :=
  Cons n (nats_from_n (S n)).
Definition nats' := nats_from_n 0.

Eval simpl in approx 10 nats.

(** We can define a stream that alternates between [true] and [false]
    using a mutual co-fixpoint (there are simpler ways, though). *)

CoFixpoint trues_falses : stream bool := Cons true  falses_trues
      with falses_trues : stream bool := Cons false trues_falses.

(* Exercise (easy): Find two more ways for constructing the stream
   which infinitely alternates the values true and false. *)
Definition trues_falses' : stream bool := iterate negb true.
Definition trues_falses'' : stream bool := interleave (repeat true) (repeat false).

(* Not every co-fixpoint is accepted by Coq, though: there are
   important restrictions that are dual to the restrictions on the use
   of inductive types. Fixpoints _consume_ values of inductive types,
   with restrictions on which _arguments_ may be passed in recursive
   calls. Dually, co-fixpoints _produce_ values of co-inductive types,
   with restrictions on what may be done with the _results_ of
   co-recursive calls. *)

(* Coq enforces that every co-recursive call must be guarded by a
   constructor; that is, every co-recursive call must be a direct
   argument to a constructor of the co-inductive type we are
   generating. For instance, the following co-fixpoint does not pass
   Coq's guardedness condition:

CoFixpoint looper : stream nat := looper.

<<
Error:
Recursive definition of looper is ill-formed.
In environment
looper : stream nat

unguarded recursive call in "looper"
>> *)

(* It is a good thing that this guardedness condition is enforced. If
   the definition of [looper] were accepted, our [approx] function
   would run forever when passed [looper], and we would have fallen
   into inconsistency. *)

(* Many other standard functions on lazy data structures (like [map],
   [iterate] and [iterate] above) can be implemented easily in Coq.
   Some, others like [filter], cannot be implemented.  (Why?) *)

(* ------------------------------------------------------------ *)
(** ** Finite Proofs about Infinite Objects *)

(* We saw that we can define recursive functions on infinite (or
   potentially infinite) objects -- e.g., approx.  We can also use the
   standard Inductive machinery to define (some) useful properties of
   potentially infinite objects. *)

Inductive finite A : llist A -> Prop :=
| fin_LNil : finite (LNil A)
| fin_LCons : forall l x, finite l -> finite (LCons x l).

(* What about defining a similar predicate [infinite]? *)

(* ------------------------------------------------------------ *)
(** ** Infinite Proofs *)

(** Suppose that we wanted to prove formally that the streams [nats]
    and [nats'] from above are equivalent. The naive way to do this is
    to state it as the following equality: *)

Theorem nats_eq : nats = nats'.
Abort.

(** However, faced with the initial subgoal, it is not at all clear
    how this theorem can be proved.  In fact, it is unprovable. The
    [eq] predicate that we use is fundamentally limited to equalities
    that can be demonstrated by finite arguments. All we can prove
    this way is that any finite approximation of [nats] and [nats']
    are equal. *)

(* First try: *)
Lemma approx_nats_eq : forall k,
  approx k nats = approx k nats'.
Proof. induction k; intros. reflexivity. simpl. Abort.

(** For this we need to work we need to first generalize the induction
    hypothesis and consider increasing streams of naturals starting
    at any natural number. *)

Lemma approx_nats_eq_helper : forall k n,
  approx k (iterate S n) = approx k (nats_from_n n).
Proof. induction k; crush. Qed.

Lemma approx_nats_eq : forall k,
  approx k nats = approx k nats'.
Proof. intros. eapply approx_nats_eq_helper. Qed.

(** In order to deal with interesting properties of infinite objects,
    it is necessary to construct infinite proofs. What we need for
    that is a _co-inductive proposition_.  That is, we want to define
    a proposition whose _proofs_ may be infinite (subject to the
    guardedness condition, of course). *)

CoInductive stream_eq (A : Type) : stream A -> stream A -> Prop :=
| Stream_eq : forall (h : A) t1 t2,
        stream_eq t1 t2
     -> stream_eq (Cons h t1) (Cons h t2).

(** We say that two streams are equal if and only if they have the
    same heads and their tails are equal.  We use normal
    finite/syntactic equality for the heads, and we refer to our new
    equality (co-)recursively for the tails. *)

(** In order to construct infinite proof terms we need to use a
    co-fixpoint, in the same way as we did for constructing infinite
    program terms. While in programming mode we used [CoFixpoint]; in
    tactic mode we can use the related [cofix] tactic for building
    co-fixpoints. *)

(** Before attacking the slightly harder problem of proving [nats] and
    [nats'] in the [stream_eq] relation, we first try to prove that
    [ones] and [ones'] are in [stream_eq]. We start by doing this
    directly using the [cofix] tactic. *)

Theorem ones_eq : stream_eq ones ones'.
  cofix.
  assumption. (* "proof completed" *)
(* Qed. --> Unguarded recursive call in "ones_eq" *)

(** The same guardedness condition applies to our co-inductive proofs
    as to our co-inductive data structures. We should be grateful that
    this proof is rejected, because, if it were not, the same proof
    structure could be used to prove any co-inductive theorem
    vacuously, by direct appeal to itself! *)

(** Looking at the proof term Coq generates from the proof script
    above, we see that the problem is that we are violating the
    guardedness condition. *)

Show Proof.
(** (cofix ones_eq  : stream_eq ones ones' := ones_eq) *)

(** During our proofs, Coq can help us check whether we have yet gone
    wrong in this way. We can run the command [Guarded] in any
    context to see if it is possible to finish the proof in a way that
    will yield a properly guarded proof term.

    Running [Guarded] here gives us the same error message that we got
    when we tried to run [Qed]. In larger proofs, [Guarded] can be
    helpful in detecting problems _before_ we think we are ready to
    run [Qed]. *)

Restart.

(** We need to start the co-induction by applying [stream_eq]'s
    constructor. To do that, we need to know that both arguments to
    the predicate are [Cons]es. Informally, this is trivial, but
    [simpl] is not able to help us, because co-fixpoint have to be
    evaluated lazily. *)

  cofix.
  simpl. (* does nothing *)
 
Abort.

(** It turns out that the simplest way to get off the ground with this
    proof is a commonly used hack. First, we need to define an
    identity function that seems pointless on first glance. *)

Definition id_force A (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

(** Next, we need to prove a theorem that seems equally pointless. *)

Theorem id_force_eq : forall A (s : stream A), s = id_force s.
Proof. destruct s; reflexivity. Qed.

(** But, miraculously, this theorem turns out to be just what we needed. *)

Theorem ones_eq : stream_eq ones ones'.
  cofix.

  (** We can use the theorem to rewrite the two streams. *)
  rewrite (id_force_eq ones).
  rewrite (id_force_eq ones').

  (** Now [simpl] is able to reduce the streams. *)
  simpl.

  (** Why did this silly-looking trick help?  The answer has to do
      with the constraints placed on Coq's evaluation rules by the
      need for termination.  The [cofix]-related restriction that
      foiled our first attempt at using [simpl] is dual to a
      restriction for [fix].  In particular, an application of an
      anonymous [fix] only reduces when the top-level structure of the
      recursive argument is known.  Otherwise, we would be unfolding
      the recursive definition ad infinitum.

      Fixpoints only reduce when enough is known about the
      _definitions_ of their arguments.  Dually, co-fixpoints only
      reduce when enough is known about _how their results will be
      used_.  In particular, a [cofix] is only expanded when it is the
      discriminee of a [match].  Rewriting with our superficially
      silly lemma wrapped new [match]es around the two [cofix]es,
      triggering reduction.

      If [cofix]es reduced haphazardly, it would be easy to run into
      infinite loops in evaluation, since we are, after all, building
      infinite objects. *)

  (** Since we have exposed the [Cons] structure of each stream, we
     can apply the constructor of [stream_eq]. *)

  constructor.
  assumption.
Qed.

(** The example above shows that one can construct infinite proofs by
    directly using [cofix], but there are two important problems with
    this. First, it's hard to keep guardedness in mind when building
    large proofs. Second, using [cofix] directly interacts very badly
    with Coq's standard automation machinery. If we try to prove
    [ones_eq] with automation we get an invalid proof. *)

Theorem ones_eq' : stream_eq ones ones'.
  cofix.
Proof.
  cofix; auto.
  (** [[
  Guarded.
  ]]
  *)
Abort.

(** The standard [auto] machinery sees that our goal matches an
    assumption and so applies that assumption, even though this
    violates guardedness.  One usually starts a proof like this by
    [destruct]ing some parameter and running a custom tactic to figure
    out the first proof rule to apply for each case.  Alternatively,
    there are tricks that can be played with "hiding" the co-inductive
    hypothesis. *)

(** However, we can devise a more principled solution to this problem
    by looking at how the dual version of the problem is generally
    solved for induction. It's equally hard to build inductive proofs
    directly using [fix], but one almost never does that. Instead one
    uses [fix] to proving general _induction principles_, and then
    simply applies those principles. *)

(** It turns out that we can usually do the same with _co-induction
    principles_. Coq will not generate co-induction principles for us
    though, so we need to define them by hand using co-fixpoints. *)

Section stream_eq_coind1.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.

  (* This is mechanically extracted from the definition of stream_eq *)
  Hypothesis H : forall s1 s2, R s1 s2 ->
    exists h, exists t1, exists t2,
      s1 = Cons h t1 /\ s2 = Cons h t2 /\ R t1 t2.

  Theorem stream_eq_coind1 : forall s1 s2 : stream A,
    R s1 s2 -> stream_eq s1 s2.
  Proof. cofix. intros s1 s2 H0. apply H in H0.
    destruct H0 as [h [t1 [t2 [H1 [H2 HR]]]]]. subst.
    apply Stream_eq. apply stream_eq_coind1. assumption.
  Qed.
End stream_eq_coind1.

(** We can now return to the proof of [ones_eq] *)

Theorem ones_eq' : stream_eq ones ones'.
Proof.
  apply stream_eq_coind1 with
    (R := fun s1 s2 => s1 = ones /\ s2 = ones'); [clear | tauto].
    (* We'll return later on how to mechanically construct the R
       from the statement of the theorem we're trying to prove.
       In this case what we do here corresponds to the [remember]
       we do before inducting on compound terms. *)
  intros s1 s2 [? ?]. subst. repeat esplit.
  rewrite (id_force_eq ones) at 1. simpl. reflexivity.
  rewrite (id_force_eq ones') at 1. simpl. reflexivity.
Qed.

(** The previous coinduction principle works, but it can be further
    simplified to reach a more standard formulation (commonly called
    Park's principle) that's easier to use in automated proofs. *)

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.

  (* We use head and tail instead of existential quantification *)
  Hypothesis H1 : forall s1 s2,
    R s1 s2 -> head s1 = head s2.
  Hypothesis H2 : forall s1 s2,
    R s1 s2 -> R (tail s1) (tail s2).

  (* We show that H1 /\ H2 is in equivalent the same as the previous H
     using existential quantification *)
  Lemma equiv : forall s1 s2, R s1 s2 ->
    ((exists h, exists t1, exists t2,
      s1 = Cons h t1 /\ s2 = Cons h t2 /\ R t1 t2)
    <->
    (head s1 = head s2 /\ R (tail s1) (tail s2))).
  Proof. clear; split; intros.
    destruct H0 as [h [t1 [t2 [H1 [H2 H3]]]]].
      subst. simpl. eauto.
    destruct H0 as [H1 H2]. 
      exists (head s1). exists (tail s1). exists (tail s2).
      destruct s1; destruct s2; simpl in *; subst; intuition.
  Qed.

  (* The proof of the coinduction principle is different; e.g. we
     don't need to use the id_force_eq trick *)
  Theorem stream_eq_coind : forall s1 s2 : stream A,
    R s1 s2 -> stream_eq s1 s2.
  Proof. cofix. intros s1 s2 H0. destruct s1. destruct s2.
    pose proof (H1 H0). simpl in *. subst.
    pose proof (H2 H0). simpl in *.
    apply Stream_eq. apply stream_eq_coind. assumption.
  Qed. (* Note: we didn't need to use the  *)

End stream_eq_coind.

(** We return again to the proof of [ones_eq] *)

Theorem ones_eq'' : stream_eq ones ones'.
Proof.
  apply stream_eq_coind with
    (R := fun s1 s2 => s1 = ones /\ s2 = ones'); crush. 
Qed.

(** This principle is better in terms of automation. Let's try to
    use it to prove that [nats] and [nats'] are in [stream_eq].*)

Lemma nats_eq : stream_eq nats nats'.
Proof.
  apply stream_eq_coind with (R := fun s1 s2 => s1 = nats /\ s2 = nats');
    crush.
  (* At this point we get two goals that are wrong:
     [iterate S 1 = nats] and [nats_from_n 1 = nats'] 
     The co-induction hypothesis is not general enough! *)
Abort.

(** In the same way we had to strengthen the inductive hypothesis in
    [approx_nats_eq_helper], here we have to strengthen the
    co-inductive hypothesis *)

Lemma nats_eq_helper : forall n,
  stream_eq (iterate S n) (nats_from_n n).
Proof.
  intro n. apply stream_eq_coind with
    (R := fun s1 s2 => exists n, s1 = iterate S n /\ s2 = nats_from_n n);
      [crush | clear | eauto].
    intros ? ? [n [? ?]]. exists (S n); crush.
Qed.

Theorem nats_eq : stream_eq nats nats'.
Proof. apply nats_eq_helper. Qed.

(** Recipe for constructing the "bisimulation" relation

You have a goal of the form:
forall x1, ..., xn,
  H1 -> ... -> Hm ->
  P t1 ... tl

Where P is a coinductively defined predicate for which you've already
defined a coinduction principle P_coind. In order to call P_coind you
need to provide a predicate R. Here is a receipe to build R.

** Step 1 (remember)

Replace any argument tj that's not a variable from xs with a fresh
variable yj, universally quantify over yj at the top and add an
additional hypothesis Hj : yj = tk. Repeat this until the goal looks
like this:

forall x1, ..., xn,
  H1' -> ... -> Hm' ->
  P y1 ... yl

** Step 2 (linearize)

If a certain y appears twice in the proposition replace one of the
occurrences with a fresh variable y' and add an equality of the form
y = y' as a hypothesis.

[You don't really need to change your goal to this, just construct
this proposition in your mind.]

[This step corresponds to "remember"-ing compound terms before
 applying induction ]
 
** Step 3 (conjunction + existentials)

Construct the conjunction of all premises H1' /\ ... /\ Hm',
and existentially quantify over all xs that are not ys:
exists x1', exists x2', ... exists xn', H1' /\ ... /\ Hm'

** Step 4 (add a lambda on top)

Chose R to be (fun y1 ... yl => 
                 exists x1', exists x2', ... exists xn',
	           H1' /\ ... /\ Hm') and you're done.
*)

(* Exercise (medium): prove that ...*)
Theorem map_iterate : forall (A:Type) (f:A->A) (x:A),
                       stream_eq (iterate f (f x)) (map f (iterate f x)).
Proof. 
Admitted.

(* Exercise: Define a co-inductive type Nat containing non-standard
natural numbers - this is, verifying
exists m : Nat, forall n : Nat, n < m. *)

(* Exercise: Prove that the equality of streams is an equivalence
   relation using the co-induction principle.  (Hint: try reflexivity
   first, then symmetry, then transitivity.) *)

(* Exercise: Provide a suitable definition of "being an ordered list"
   for infinite lists and define a principle (similar to the Park
   principle) for proving that an infinite list is ordered.  Apply
   this method to the stream [nats].  

   Hint: There are different ways of formulating the definition.  If
   you find yourself having trouble proving things, back up and see if
   you can state the definition a different way. *)

