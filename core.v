Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.


Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export CoRN.ftc.MoreIntervals.

(* Definition N2Q (n: nat) : Q := n. *)


(* Coercion N2Q : nat >-> Q. *)

Definition ninv (n: nat) : Q :=
  Qinv (n).

Definition R := IR.

Require Export Coq.ZArith.ZArith.

Definition Q2R  (q: Q) : R := (inj_Q IR q).

Definition N2R  (n: nat) : R := (inj_Q IR  n).

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

Definition RNonNeg := RInInterval (closel [0]).
Definition RPos := RInInterval (openl [0]).

Definition restrictToInterval {A} (f : R -> A) 
    (intvl : interval) : (RInInterval intvl) -> A :=
    fun r => f r.


Definition Time := RNonNeg.
Open Scope Q_scope.


Definition Qpos : Type := {q : Q | 0 < q}.

Definition Qp2Q (t : Qpos) : Q := (proj1_sig t).
Coercion Qp2Q : Qpos >-> Q.

(*
Definition Time : Type := {q : Q | 0 <= q}.
Definition T2Q (t : Time) : Q := (proj1_sig t).
Coercion T2Q : Time >-> Q.
*)

(*
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
*)

Definition tdiff (t tl : Time) : Time.
(*  exists (Qabs (tl - t)).
  apply Qabs_nonneg. *)

  exists (AbsIR (tl [-] t)).
  unfold iprop. apply AbsIR_nonneg.
Defined.

 
 Definition tadd (t tl : Time) : Time.
   exists (tl [+] t).
   unfold iprop. destruct t. destruct tl.
   simpl. unfold iprop in realVPos0.
   unfold iprop in realVPos1.
   eauto with *.
(*   exists (tl + t). destruct t, tl. simpl.
  apply Q.Qplus_nonneg; auto. 
*)
 Defined.

 Lemma N2RNonNeg : forall n, [0][<=]N2R n.
 Proof.
   intro n. unfold N2R. rewrite <- inj_Q_Zero.
   apply inj_Q_leEq.
   apply Q.Qle_nat.
 Qed.

 Definition N2T (n: nat) : Time.
   exists (N2R n). unfold iprop.
   apply N2RNonNeg.
 Defined.


Coercion N2T : nat >-> Time.
  (* Q.Qle_nat *)

(*
Definition fastFwdAndRestrict {A}
    (f : Time -> A) (tstart tend : Time) :
      (RInInterval (clcr [0] (tdiff tend tstart))) -> A :=
restrictTill (fastFwd f tstart) (tdiff tend tstart).
*)

Definition equalUpto {Value : Type} (t: Time) (f1 f2 : Time -> Value) :=
  forall  (ti: Time), (ti [<=] t) -> f1 ti = f2 ti.

Set Implicit Arguments.

Definition ConjL (lp : list Prop) : Prop := (fold_left (fun A B => A/\B) lp True).
 

Inductive Cast (T: Type) : Prop :=
cast : T -> Cast T.


Require Import String.


Definition InjectiveFun {A B} (f : A -> B) :=
  forall (a1 a2: A), f a1 = f a2 -> a1 = a2.

Class UniqueNames (T : Type) :=
{
    tname : T -> string;
    tnameInj : InjectiveFun tname
}.

Class DecEq (T : Type) :=
{
    eqdec : forall (a b :T), {a=b} + {a<>b}
}.



Definition boolToProp (b : bool) : Prop :=
match b with
| true => True
| false => False
end.

Open Scope R_scope.
Definition enqueue {A : Type} 
    (el : A) (oldQueue : list A) : list A :=
    el :: oldQueue.

Definition dequeue {A : Type} (l: list A) : option A * list A :=
match rev l with
| nil => (None, nil)
| last :: rest => (Some last, rev rest)
end.

Require Export CoRN.reals.Q_in_CReals.

Definition Z2R  (n: Z) : R := (inj_Q IR  n).

Definition overApproximate (t: R) : { z:  Z | t  [<] Z2R z}.
  remember (start_of_sequence _ t).
  clear Heqs. destruct s as [qf Hp]. destruct Hp as [qc Hpp].
  exists (Qround.Qceiling qc).
  unfold Z2R. pose proof (Qround.Qle_ceiling qc) as Hq.
  apply (inj_Q_leEq IR) in Hq.
  eauto  using less_leEq_trans.
Defined.

(*
Definition overApproximateN (t: R) : { n: nat | t  [<] N2R n}.
destruct (overApproximate t) as [zf  Hp].
exists (Z.to_N zf).
*)


Definition RTime :=Time.


Lemma N2R_add_commute : forall (n1 n2 : nat),
  N2R n1 [+] N2R n2 = N2R (n1 + n2).
Abort.


(** Much of the work in defining devices is to decide what the inputs
    and outputs are and what property they specify. Each device is defined
    in it's own file *)

Close Scope R_scope.


(** A [TimeFun] is a partial function from reals to reals,
   such that its domain includes the non-negative reals.
   From this, one can extract a member of [Time -> R]
   representing how the physical quantity changed over time.
  [PartIR] ensures functionality, unlike  [Time -> R] *)
Record TimeFun := 
 { f :> PartIR ;
  definedOnNonNeg : included (closel [0]) (pfdom _ f)
}.

Definition getF  (f : TimeFun)  (t :Time ) : R :=
f t ((definedOnNonNeg f) _ (realVPos _ t)).


Definition isDerivativeOf (F' F : TimeFun) : CProp :=
Derivative (closel [0]) I F F'.

Require Export CoRNMisc.
Lemma TDerivativeUB :forall {F F' : TimeFun}
   (ta tb : Time) (Hab : ta[<]tb) (c : R),
   isDerivativeOf F' F
   -> UBoundInCompInt Hab F' c
   -> ((getF F) tb[-] (getF F) ta)[<=]c[*](tb[-]ta).
Proof.
 intros ? ? ? ? ? ? Hisd Hub.
 unfold getF. 
 apply (AntiderivativeUB2 F F' ta tb Hab); auto.
 unfold isDerivativeOf in Hisd.
 eapply Included_imp_Derivative;
 [ apply Hisd | ].
 

