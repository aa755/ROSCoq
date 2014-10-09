Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.


Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export CoRN.reals.CReals1.
Require Export CoRN.ftc.MoreIntervals.

Definition N2Q (n: nat) : Q :=
  (inject_Z (Z_of_nat n)).


Coercion N2Q : nat >-> Q.

Definition ninv (n: nat) : Q :=
  Qinv (n).

Definition R := IR.

Require Export Coq.ZArith.ZArith.

Definition Q2R  (q: Q) : R := (inj_Q IR q).

Definition N2R  (n: nat) : R := (inj_Q IR (N2Q n)).

(* Coercion Q2R : Q >-> IR. *)

(** Time is modeled as a real number. One is allowed to make non-deterministic
   decisions on time *)



Notation "a < b < c" := (Qlt a  b /\  Qlt b  c) : Q_scope .


Notation "A & B" := (prod A B)  (at level 80, right associativity).
Notation "a < b < c" := (a [<] b &  b [<] c) : R_scope.
Notation "a <= b <= c" := (a [<=] b &  b [<=] c) : R_scope.



Record RInInterval (intvl : interval)  := {
  realV :> R;
  realVPos : iprop intvl realV
}.

Definition Rpos := RInInterval (closel [0]).

Definition restrictToInterval {A} (f : R -> A) 
    (intvl : interval) : (RInInterval intvl) -> A :=
    fun r => f r.


Definition Time := Rpos.

Lemma restrictTill {A} (f : Time -> A) 
    (right : Time) : (RInInterval (clcr [0] right)) -> A.
  intro rint.
  destruct rint.
  apply f. exists realV0.
  unfold iprop.
  unfold iprop in realVPos0.
  destruct realVPos0.
  trivial.
Defined.

Lemma fastFwd {A} (f : Time -> A) 
    (duration : Time) : Time  -> A.
  intro rint.
  destruct rint.
  apply f. exists (realV0 [+] duration).
  destruct duration. simpl.
  unfold iprop.
  unfold iprop in realVPos0.
  unfold iprop in realVPos1.
  eauto with *.
Defined.

Definition tdiff (t tl : Time) : Time.
  exists (AbsIR (tl [-] t)).
  unfold iprop.
  apply AbsIR_nonneg.
Defined.

Definition tadd (t tl : Time) : Time.
  exists (tl [+] t).
  unfold iprop. destruct t. destruct tl.
  simpl. unfold iprop in realVPos0.
  unfold iprop in realVPos1.
  eauto with *.
Defined.

Definition t0 : Time.
  exists [0]. unfold iprop.
  apply leEq_reflexive.
Defined.



Definition fastFwdAndRestrict {A}
    (f : Time -> A) (tstart tend : Time) :
      (RInInterval (clcr [0] (tdiff tend tstart))) -> A :=
restrictTill (fastFwd f tstart) (tdiff tend tstart).


Definition equalUpto {Value : Type} (t: R) (f1 f2 : Time -> Value) :=
  forall  (ti: Time), (ti [<=] t) -> f1 ti = f2 ti.

Set Implicit Arguments.

Definition ConjL (lp : list Prop) : Prop := (fold_left (fun A B => A/\B) lp True).
 

Inductive Cast (T: Type) : Prop :=
cast : T -> Cast T.

Open Scope R_scope.


(** Much of the work in defining devices is to decide what the inputs
    and outputs are and what property they specify. Each device is defined
    in it's own file *)

Close Scope R_scope.
