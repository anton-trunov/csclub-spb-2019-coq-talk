(** Use some very basic facilities of mathcomp library *)
From mathcomp Require Import ssreflect ssrfun seq.

Module My.
(** We introduce these definitions inside a new module
    to avoid name clashes with the standard library later *)

Inductive bool : Type :=
| true
| false.

Check true : bool.
Check true.

(** Definitions (not part of Coq's type theory, by the way, it's
    a meta-linguistic feature) *)
Definition idb := fun b : bool => b.
Definition id := fun A : Type =>
                 fun a : A => a.
Check id.

(** Pattern-matching *)
Definition negb (b : bool) :=
  match b with
  | true => false
  | false => true
  end.

Compute idb true.
Compute idb false.
Arguments id {A}.
Compute id false.
Compute @id _ false.

Compute negb true.
Compute negb false.

Definition andb (b c : bool) : bool :=
  match b with
  | true => c
  | false => false
  end.



(** Peano numbers -- the first truly inductive type *)
Inductive nat : Type :=
| S of nat
| O.
Print nat.

Check O.
Check S.
Check (S O).
Check S (S O).
Check S (S (S O)).

Definition inc2 (n : nat) := S (S n).
Compute inc2 (S (S O)).

(** predecessor function *)
Definition pred (n : nat) : nat :=
  match n with
  | S n' => n'
  | O => O   (* truncation! Coq's functions are total *)
  end.

(**
Some options to go about implementing [pred] function:

 pred : nat -> nat  (* way to go *)
 pred : nat -> option nat
 pred : forall n : nat, (n <> 0) -> nat
*)

(** Addition of natural numbers *)

(** [{struct n}] means structural recursion on parameter [n].
    Coq can infer the [struct] annotation in this case. *)

Fixpoint addn (n m : nat) {struct n} : nat :=
  match n with
  | S n' => S (addn n' m)
  | O => m
  end.

Fixpoint addn' (n m : nat) {struct m} : nat :=
  match m with
  | S m' => S (addn' n m')
  | O => n
  end.

Compute addn (S (S O)) (S (S O)).  (* 2 + 2 is 4 *)


Fixpoint muln (n m : nat) : nat :=
  match n with
  | S n' => addn m (muln n' m)
  | O => O
  end.

Compute muln (S (S (S O))) (S (S O)).  (* 3 * 2 is 6 *)
Compute muln (S (S O)) O.              (* 2 * 0 is 0 *)



(** Let's illustrate why "in the empty context" is important *)
Check (fun f : False => f (* here we construct a value of type
                             [False], but the context is not empty,
                             since the function parameter becomes
                             part of context here *)
      ).
(** Since it's impossible to construct a value of an empty type,
    it's impossible to call a function of type
    False -> SomeType *)
(** ... provided we are talking about empty contexts again: *)
Check (fun g : False =>
         (fun f : False => f) g     (* call [fun f : False => f]
                                       with [g] as the argument *)
      ).
End My.



Set Implicit Arguments.

Module MyNamespace.

(** Motivation to introduce product type.
    Euclidean division: returns quotient and reminder  *)

(** Type constrtuctors, Product type *)

Section ProductType.

Inductive prod (A B : Type) : Type :=
  | pair of A & B.

About pair.

(** Explicit binding of type constructor's parameters for
    data constrtuctors
  *)
Check pair 42 true : prod nat bool.
Check @pair nat bool 42 true : prod nat bool.

(** Implicit arguments;
    local deactivation of implicit arguments (@)
 *)

Check @pair nat bool 42 true.




(** Notations for better UX *)
Notation "A * B" := (prod A B) (at level 40, left associativity)
                    : type_scope.

Notation "( p , q , .. , r )" := (pair .. (pair p q) .. r)
                                   : core_scope.

Check (1, false) : nat * bool.

Unset Printing Notations.
Check (1, false) : nat * bool.
Set Printing Notations.

Definition fst {A B : Type} : A * B -> A :=
  fun '(a, _) => a.

Definition snd {A B : Type} : A * B -> B :=
  fun '(a, b) => b.

Definition swap {A B : Type} : A * B -> B * A :=
  fun '(a,b) => (b,a).

End ProductType.

(**
      A /\ B -> B /\ A
 *)


Section Intuitionistic_Propositional_Logic.

(** Implication *)

Definition A_implies_A (A : Prop) :
  A -> A
:=
  fun proof_A : A => proof_A.

Definition A_implies_B_implies_A (A B : Prop) :
  A -> B -> A
:=
  fun proof_A => fun proof_B => proof_A.
(* const *)


(** Conjunction *)

Inductive and (A B : Prop) : Prop :=
  | conj of A & B.

Notation "A /\ B" := (and A B) : type_scope.

Definition andC (A B : Prop) :
  A /\ B -> B /\ A
:=
  fun '(conj proof_A proof_B) => conj proof_B proof_A.

Definition andA (A B C : Prop) :
  (A /\ B) /\ C -> A /\ (B /\ C)
:=
  fun '(conj (conj a b) c) => conj a (conj b c).


(** Biimplication, a.k.a. if and only if *)

Definition iff (A B : Prop) : Prop :=
  (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

Definition andA_iff (A B C : Prop) :
  (A /\ B) /\ C <-> A /\ (B /\ C)
:=
  conj
    (fun '(conj (conj a b) c) => conj a (conj b c))
    (fun '(conj a (conj b c)) => (conj (conj a b) c)).


(** Disjunction *)

Inductive or (A B : Prop) : Prop :=
| or_introl of A
| or_intror of B.

Arguments or_introl [A B] a, [A] B a.
Arguments or_intror [A B] b, A [B] b.

Notation "A \/ B" := (or A B) : type_scope.

Definition or1 (A B : Prop) : A -> A \/ B
  :=
fun proofA => or_introl proofA.

Definition orC A B :
  A \/ B -> B \/ A
:=
  fun a_or_b =>
    match a_or_b with
    | or_introl proofA => or_intror proofA
    | or_intror proofB => or_introl proofB
    end.

Definition or_and_distr A B C :
  (A \/ B) /\ C -> (A /\ C) \/ (B /\ C)
:=
  fun '(conj a_or_b c) =>
    match a_or_b with
    | or_introl a => or_introl (conj a c)
    | or_intror b => or_intror (conj b c)
    end.

Inductive False : Prop := .

Inductive True : Prop :=
  | I.

Definition t : True
  :=
I.

Definition t_and_t : True /\ True
  :=
conj I I.

Definition not (A : Prop) :=
  A -> False.

Notation "~ A" := (not A) : type_scope.

Definition A_implies_not_not_A (A : Prop) :
   A -> ~ ~ A
(* A -> (A -> False) -> False *)
:=
  fun a => fun not_a => not_a a.

(* Double negation elimination is
   not provable in Intuitionistic Logic *)
Fail Definition DNE (A : Prop) :
   ~ ~ A -> A
:=
  fun nna => __.  (* can't call [nna] *)

(* Since the Law of Exlcluded Middle
   is equivalent to DNE it's not provable
   either
 *)
Fail Definition LEM (A : Prop) :
   ~ ~ A \/ ~A
:=
  (* or_intror (fun a => ???). *)
  __. (* or_introl / or_intror ? *)

End Intuitionistic_Propositional_Logic.

End MyNamespace.


(** The SSReflect proof language *)

Definition swap' (A B : Type) : A * B -> B * A.
  Show Proof.
  case.
  Show Proof.
  move=> a.
  move=> b.
  Show Proof.
  split.
  exact: b.
  exact: a.
Defined.
Print swap'.

Lemma andC (A B : Prop) : A /\ B -> B /\ A.
Proof.
  case.
  move=> pa pb.
  split.
  exact: pb.
  exact: pa.
Qed.


(* obligatory proof of associativity of some concrete monoid's operation :) *)

Lemma catA : forall (T : Type) (xs ys zs : seq T),
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
move=> T xs ys zs.
by elim: xs => // x xs' /= ->.
Qed.



(*** Dependent types *)


(** * A rather silly example *)

Definition Foo (b : bool) : Type :=
  if b then nat else bool.

Fail Definition bar (b : bool) : Foo b :=
  if b return _ then 0 else false.

Definition bar (b : bool) : Foo b :=
  if b as b' return (Foo b') then 42 else false.



(*** Totality *)

(* A plugin to control the guardedness check, strict positivity rule, etc.
   It's not needed with the current development version of Coq.
   https://github.com/SimonBoulier/TypingFlags

   Usage:
   From TypingFlags Require Import Loader.
 *)

(* Disable termination checking of fixpoints *)

(* WARNING: the rest tof this file only works
            with the current master branch of Coq *)
Unset Guard Checking.

(** * Elegant, but non-structural recursive [interleave] function *)

Fixpoint interleave_ns {T} (xs ys : seq T) {struct xs} : seq T :=
  if xs is (x :: xs') then x :: interleave_ns ys xs'
  else ys.

Compute interleave_ns [:: 1; 3] [:: 2; 4].

(* simple unit tests *)
Check erefl : interleave_ns [::] [::] = [::].
Check erefl : interleave_ns [::] [:: 1] = [:: 1].
Check erefl : interleave_ns [:: 1] [::] = [:: 1].
Check erefl : interleave_ns [:: 1; 3] [:: 2; 4] = [:: 1; 2; 3; 4].
Check erefl : interleave_ns [:: 1] [:: 2; 3] = [:: 1; 2; 3].

Print Assumptions interleave_ns.



Fixpoint interleave {T} (xs ys : seq T) : seq T :=
  match xs, ys with
  | (x :: xs'), (y :: ys') => x :: y :: interleave xs' ys'
  | [::], _ => ys
  | _, [::] => xs
  end.

Check erefl : interleave [::] [::] = [::].
Check erefl : interleave [::] [:: 1] = [:: 1].
Check erefl : interleave [:: 1] [::] = [:: 1].
Check erefl : interleave [:: 1; 3] [:: 2; 4] = [:: 1; 2; 3; 4].
Check erefl : interleave [:: 1] [:: 2; 3] = [:: 1; 2; 3].

Lemma interleave_ns_eq_interleave {T} (xs ys : seq T) :
  interleave_ns xs ys = interleave xs ys.
Proof.
by elim: xs ys => //= x xs' IHxs' [|y ys'] //=; rewrite IHxs'.
Qed.

(** More ways of implementing [interleave] can be found here:
    https://stackoverflow.com/a/48178543/2747511
 *)




(** * Why do we require termination? *)

(** Let's prove False! *)

Fixpoint proof_of_False (n : nat) : False :=
  proof_of_False n.

Check proof_of_False 0.

Print Assumptions proof_of_False.



(** Remark: Coq's implementation
    does not enforce strong normalization *)
Set Guard Checking.

Fixpoint weak (n : nat) : nat :=
  let bar := weak n in
  0.
Print Assumptions weak.





(** * Strict positivity rule *)

Unset Positivity Checking.

Inductive prop :=
  RemoveNegation of (prop -> False).

Definition not_prop (p : prop) : False :=
  let '(RemoveNegation not_p) := p in not_p p.
Check not_prop : prop -> False.

Check RemoveNegation not_prop : prop.

Definition yet_another_proof_of_False : False :=
  not_prop (RemoveNegation not_prop).

Print Assumptions yet_another_proof_of_False.





(** * Type : Type *)

Check Type : Type.

Set Printing Universes.

Universe i j.

Fail Check Type@{i} : (Type@{i}).

Check Type@{i} : (Type@{j}).

Check nat.
Check Set.


Unset Universe Checking.

Check Type.
Check Type@{i} : (Type@{i}).
(* Deriving a contradiction here is less trivial and is left for a future talk *)

(* It's not possible to derive a fixed point combinator if we have Type : Type,
   but one can define a family of looping combinators:
    Y0, Y1, Y2 ...
satisfying the property
    Yi F = F(Y{i+1} F)
This is enough to type all partial recursive functions.
*)

Set Universe Checking.


Unset Printing Universes.

(* If you want more:
   "One Monad To Prove Them All" by J. Christiansen, S. Dylus, F. Teegen(2018)
   https://arxiv.org/abs/1805.08059
 *)


(** * Impredicativity of Prop *)

Check (forall P : Prop, P) : Prop.

Fail Check (forall P : Type@{i}, P) : (Type@{i}).
