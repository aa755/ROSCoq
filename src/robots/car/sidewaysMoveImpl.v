(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)
(** printing ≡ $\equiv$ #≡# *)
(** printing [*] $*$ #*# *)
(** printing ∧ $\wedge$ #∧# *)
(** printing ∀ $\forall$ #∀# *)
(** printing → $\rightarrow$ #→# *)
(** printing ∃ $\exists$ #∃# *)
(** printing ≤ $\le$ #≤# *)
(** printing θ $\theta$ #θ# *)
(** printing eeev $\epsilon_v$ #∊ᵥ# *)
(** printing eeew $\epsilon_w$ #∊w# *)
(** printing tm $t_m$ #tm# *)
(** printing IR $\mathbb{R}$ #IR# *)
(** printing CR $\mathbb{R}$ #CR# *)
(** printing tr $t_r$ #tr# *)
(** remove printing * *)

(** printing ' $ $ #'# *)

Set Suggest Proof Using.

Require Import Vector.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import robots.car.ackermannSteering.
Require Import MCMisc.tactics.
Require Import CartIR.
Require Import fastReals.interface.
Require Import fastReals.misc.
Require Import geometry2D.
Require Import geometry2DProps.
Require Import robots.car.ackermannSteeringProp.
Require Import MathClasses.orders.rings.
Require Import MathClasses.interfaces.orders.
Require Import robots.car.atomicMoves.
Require Import IRMisc.LegacyIRRing.
Hint Unfold One_instance_IR : IRMC.
Require Import robots.car.firstQuadrant.

  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).
  Local Notation  "∫" := Cintegral.
  Local Notation ConfineRect := (Line2D).

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Require Import CartIR2.

Require Import robots.car.exampleDimensions.
Require Import robots.car.sidewaysMove.

(** In [sidewaysMove], we analyzed the space needed to execute
a sideways move, which is specified by 3 parameters.
To implement such a move, one has to invert that equation --
given the amount of available space, find a best
choice of those 3 parameters.
We fix one of those by deciding that while turning, the
steering wheel will be at its extremities -- this choice
may be optimal.

2 parameters remain : how much to drive while turning,
and how much to drive while moving straight.
The total X-space needed can be decomposed as a sum
of 2 terms, each of which is a function of these 2 parameters. 
The latter function, which
is the X-space consumed by the straight move, is easily
invertible. The former, which is
the space needed to execute the [Wriggle] part of the sideways move,
is a horrendous quartic -- will be solved numerically, and only approximately.
(It may be possible to solve it exatly.)

There is a meta parameter [k] denoting what fraction of the available
X-space is spent on doing Wriggle. The upward shift (the larger, the better) 
is 0 for both extremes of this paremeter (0 and 1).
If wriggle is done without consuming any extra space, no turn will
be produced, and hence the straight move in the middle will result
in  0 upward shift. On the other hand, if all the space 
is spent on wriggle, the
car will turn a lot, but return to its original position
 (Wriggle + WriggleInv == 0).
We will try many choices of this [k], and pick the best among those.

The proof only says that the sideways move will be safe, and
produce a positive upward shift. Depending on how carefully the
parameter [k] is chosen, a possibly approximate optimality theorem
may be proven.
*)

Section InverseProblem.

Variable cg : CarGeometry Q.

(*Move*)
Definition nonTrivialCarGeometry (cd : CarGeometry Q) : Prop := 
nonTrivialCarDim (carDim cd) /\ 0 < minTR cd.

Hypothesis ntriv : nonTrivialCarGeometry cg.

Let tr : Q := minTR cg.

Definition α : Q := Qinv tr.

Lemma αPos : ((0:IR)[<]'α).
Proof using ntriv.
  eapply less_wdl;[| apply inj_Q_Zero].
  apply inj_Q_less.
  apply Qinv_lt_0_compat.
  apply ntriv.
Qed.

Let αNZ := ((pos_ap_zero _ _ αPos): 'α[#](0:IR)).

Local Definition trComplicated : 'tr = f_rcpcl ('α) αNZ.
Proof using ntriv.
  rewrite <- Qinv_involutive.
  apply QinvIRinv.
Qed.

(** The turn center cannot be inside the car. for that,
one of the front wheels have to rotate by more than 90 along 
the vertical axis. 
*)
Let cd : CarDimensions Q:= carDim cg.
Hypothesis turnCentreOut : ((width cd) <= tr)%Q.

Local Definition βMinusBack : Cart2D Q := CornerAngles.βMinusBack cd tr.
Local Definition βMinusFront : Cart2D Q := CornerAngles.βMinusFront cd tr.
Local Definition βPlusBack : Cart2D Q := CornerAngles.βPlusBack cd tr.
Local Definition βPlusFront : Cart2D Q := CornerAngles.βPlusFront cd tr.

(** extra space available t execute the sideways move *)
Variable Xs : Q.
Hypothesis Xsp : (0<Xs).

(** space needed for the wriggle move for a given θ. The parameter
[d] that we are after is just [θ/α] *)
Let extraSpaceX1  : CR → CR := extraSpaceX1 α cd.

Section Safety.

(** we will analyse whether a given [d] is safe, 
and quantify its upward shift *)
Variable d:Q.
Let init  := (0:Rigid2DState IR).
Let SWriggle := (Wriggle ('α) αNZ ('d)).

  
End Safety.


(** explained above : fraction of the X space which can be consumed 
while doing Wriggle *)
Variable k : Q.
Hypothesis  kIsFrac : (0<k<1).

(** extra space available to execute wriggle *)
Definition Xw : Q := Xs * k.

Lemma XwPos : 0<Xw.
Proof using Xsp kIsFrac ntriv tr.
  unfold Xw.
  autounfold with QMC in *.
  unfold Qlt in *. 
  (* reduce to a problem in Z, which nia knows about*)
  simpl in *.
  nia.
Qed.

Require Import implCR.


Let XSpaceMonotoneUB : CR := XSpaceMonotoneUB α cd.

Let extraSpaceX1AtUB : CR := extraSpaceX1 XSpaceMonotoneUB.

(** we need to often compare reals. This can
only be done upto a finte (but arbitrary) accuracy.*)
Variable eps : Qpos.

Let extraSpaceX1AtUBQ : Q := 
  (approximate extraSpaceX1AtUB eps).

Definition bisectionSearchNeeded : bool := 
  bool_decide ((Xw - (eps:Q)) ≤ extraSpaceX1AtUBQ).
  
Require Import MathClasses.implementations.bool.

Section Case1.
  Hypothesis case1 : bisectionSearchNeeded = true.
  
  Lemma case1Condition :  extraSpaceX1AtUB < 'Xw.
  Abort.
  
End Case1.


Section Case2.
  Hypothesis case2 : bisectionSearchNeeded = false.

Typeclasses eauto :=2.
Local Opaque bool_decide_false.

(*
  Lemma case1Condition :  extraSpaceX1AtUB < 'Xw.
  Proof using case2*.
    pose proof case2 as cc.
    unfold bisectionSearchNeeded in cc.
    unfold equiv, bool_eq in cc.
    unfold bool_decide in cc.
    match type of cc with
      context[if ?d then _ else _] => destruct d;[discriminate|]
    end. clear cc. rename n into cc.
    apply Qnot_le_lt in cc.
    unfold extraSpaceX1AtUBQ in cc.
    eapply le_lt_trans;
      [apply upper_CRapproximation with (e:=eps)|].
    apply (@strictly_order_preserving _ _ _ _ _  _ _ _).
    autounfold with QMC in *.
    lra.
  Qed. (** for some reason, coq takes forever at this Qed*) 
*)
(*
  Lemma case1Condition :  extraSpaceX1AtUB < 'Xw.
  Proof using case2*.
    unfold bisectionSearchNeeded in case2.
    apply bool_decide_false, Qnot_le_lt in case2.
    unfold extraSpaceX1AtUBQ in case2.
    eapply le_lt_trans;
      [apply upper_CRapproximation with (e:=eps)|].
    apply (@strictly_order_preserving _ _ _ _ _  _ _ _).
    autounfold with QMC in *.
    lra.
    Show Proof.
  Defined.
  (** for some reason, coq takes forever at this Qed.
  this problem happens after using [bool_decide_false]*) 
*)
  
End Case2.


End InverseProblem.