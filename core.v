Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.

Definition N2Q (n: nat) : Q :=
  (inject_Z (Z_of_nat n)).


Coercion N2Q : nat >-> Q.

Definition ninv (n: nat) : Q :=
  Qinv (n).

Record R : Set := {
  seq : nat -> Q;
  seqReg : forall (n m : nat), 
      Qabs ((seq n) -  (seq m)) < ((ninv (S n) + ninv (S m)))
}.

Require Export Coq.ZArith.ZArith.

Lemma auxN2R : forall n n0 m : nat, Qabs (n - n) < ninv (S n0) + ninv (S m).
Proof.
  intros. simpl.
  unfold ninv.
  simpl.
  rewrite <- Zopp_mult_distr_l.
  rewrite (Ropp_def Zth).
  simpl. eauto with *.
Qed.


Definition N2R (n: nat) : R.
Proof.
  eapply Build_R with (seq := fun m => n).
  intro. apply auxN2R.
Defined.


Coercion N2R : nat >-> R.

(** Time is modeled as a real number. One is allowed to make non-deterministic
   decisions on time *)


Definition Rlt (s1 s2 : R) : Set :=
{n : nat &  (seq s2 n) - (seq s1 n) > ninv (S n) }.

Definition Rgt (s1 s2 : R) : Set := Rlt s2 s1.


Notation "a < b < c" := (Qlt a  b /\  Qlt b  c) : Q_scope .

Delimit Scope R_scope with R.
Infix "<" := Rlt : R_scope.
Infix ">" := Rgt : R_scope.


Notation "A & B" := (prod A B)  (at level 80, right associativity).
Notation "a < b < c" := (Rlt a  b & Rlt b  c) : R_scope.


Definition Rle (s1 s2 : R) : Set :=
forall (n : nat), ((seq s2 n) - (seq s1 n)) > -ninv (S n).

Infix "<=" := Rle : R_scope.

Lemma RleRefl : forall (t : R), Rle t t.
Admitted.

Open Scope R_scope.


Notation CProp := Type.


(** Devices are parametrized by an input type and and output type.
    If there are multiple input or outputs, one can use
    Coq's product types to combine them into a "bundle".
    (Just for fun, note that one can use dependent products 
      to model an unbounded number of inputs)


  One just postulates the existence
  of this device, they don't get any information about how
  the input relates to the output. 
   
   These devices model what is already there on the hardware, so
   we don't expect anyone to instantiate these devices to model
   the hardware, because the specs of hardware ususally are never
   detailed enough to exactly predict the output 
   One can only make some assumptions about how the
   output at some time relates to the input at previous times.

   To make some assumption
*)

Open Scope R_scope.

Record Rpos := {
  realV :> R;
  realVPos : O <= realV
}.

(* Notation "R+" := Rpos : type_scope. *)

Definition Time := Rpos.

Definition equalUpto {Value : Type} (t: R) (f1 f2 : Time -> Value) :=
  forall  (ti: Time), (ti <= t) -> f1 ti = f2 ti.

Set Implicit Arguments.


Inductive Cast (T: Type) : Prop :=
cast : T -> Cast T.

Definition RInterval (left right: R) :=
{r : R |  Cast (Rlt left r) /\ Cast (Rlt r right)}.
  
(** Much of the work in defining devices is to decide what the inputs
    and outputs are and what property they specify. Each device is defined
    in it's own file *)

Close Scope R_scope.
Open Scope Q_scope.
(*
Class Equiv A := equiv: A -> A -> Set.
Infix "==" := equiv: type_scope.


Instance SameLimit : Equiv R := 
  fun s1 s2 => (forall (n : nat), 
  Qabs ((seq s1) n - (seq s2) n) < 2 * (ninv (S n))).

*)
Lemma rle_trans : forall (r1 r2 r3 : R),
  Rle r1 r2
  -> Rle r2 r3
  -> Rle r1 r3.
Admitted.

Close Scope Q_scope.
