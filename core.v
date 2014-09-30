Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.


Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export CoRN.reals.CReals1.


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



Record Rpos := {
  realV :> R;
  realVPos : [0] [<=] realV
}.


Definition Time := Rpos.

Definition equalUpto {Value : Type} (t: R) (f1 f2 : Time -> Value) :=
  forall  (ti: Time), (ti [<=] t) -> f1 ti = f2 ti.

Set Implicit Arguments.


Inductive Cast (T: Type) : Prop :=
cast : T -> Cast T.

Open Scope R_scope.
Definition RInterval (left right: R) :=
{r : R |  left <= r <= right}.
  
(** Much of the work in defining devices is to decide what the inputs
    and outputs are and what property they specify. Each device is defined
    in it's own file *)

Close Scope R_scope.
