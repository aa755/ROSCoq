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
Require Import MathClasses.implementations.bool.

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

Variable cd : CarDimensions Q.

(*Move*)
Definition nonTrivialCarGeometry (cd : CarGeometry Q) : Prop := 
nonTrivialCarDim (carDim cd) /\ 0 < minTR cd.

Hypothesis ntriv : nonTrivialCarDim cd.

Variable  α : Q.
Hypothesis αPosQ : (0<α).


Let αPos : ((0:IR)[<]'α).
Proof using αPosQ.
  eapply less_wdl;[| apply inj_Q_Zero].
  apply inj_Q_less. apply αPosQ. 
Qed.

Let tr :=  Qinv α.

Hint Resolve  αPos : sideways.
Let αNZ := ((pos_ap_zero _ _ αPos): 'α[#](0:IR)).

Let trComplicated : 'tr = f_rcpcl ('α) αNZ.
Proof using ntriv.
 apply QinvIRinv.
Qed.

(** The turn center cannot be inside the car. for that,
one of the front wheels have to rotate by more than 90 along 
the vertical axis. 
*)
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
Let extraSpaceX1W  : CR → CR := 
  sidewaysMove.extraSpaceX1 α cd.


(** Recap:
[extraSpaceX1W] is valid only for 
when [(α * d)] is  between 0 and [leftCriticalAngle].
There is also an [extraSpaceX2] for the case when
[(α * d)] is between [leftCriticalAngle]
and [(polarTheta βPlusBack)/2], however that 
range may be so small for most cars, that 
it is not worth analysing that equation.
For mazda 3, the range was 2 degrees.
Beyond [(polarTheta βPlusBack)/2], the problem
becomes trivial, and can be solved in just 1 move.
*)

Let leftCriticalAngle : CR := 
  sidewaysMove.leftCriticalAngleCR  α cd.

(** the srict inequality in the 
last clause is necessary, because we want 
same space to be left for the straight move,
to ensure that 
the upward is nonzero. *)
Definition dAdmissibleXwise (d:CR) :=
0 ≤ d ≤ ('tr) * leftCriticalAngle
/\ d ≤ (('Qmake 1 4)*π)
/\ extraSpaceX1W ('α * d) < 'Xs.

(** we need to often compare reals. This can
 -only be done upto a finte (but arbitrary) accuracy.*)
Variable eps : Qpos.
 
(* Move *)
Definition approxDecLtRQ (a:CR) (b:Q) : bool :=
let aq : Q := approximate a eps in
bool_decide (aq + eps < b).


(* Move *)
Lemma approxDecLtRQSound: forall (a:CR) (b:Q),
approxDecLtRQ a b = true
-> a < 'b.
Proof using.
  intros ? ? H.
  apply bool_decide_true in H.
  eapply le_lt_trans;
    [apply upper_CRapproximation with (e:=eps)|].
  apply (@strictly_order_preserving _ _ _ _ _  _ _ _).
  exact H.
Qed.

(* Move *)
Lemma approxDecLtRQApproxComplete: forall (a:CR) (b:Q),
a < '(b - 2*`eps)
-> approxDecLtRQ a b = true.
Proof using.
  intros ? ? H.
  apply bool_decide_true.
  rewrite preserves_minus in H.
  apply flip_lt_minus_l  in H.
  rewrite negate_involutive in H.
  apply (@strictly_order_reflecting _ _ _ _ _
      _ (@cast Q CR _) _).
  eapply le_lt_trans;[| apply H]. clear H.
  apply flip_le_minus_l.
  eapply transitivity;
    [|apply lower_CRapproximation with (e:=eps)].
  rewrite <- (@preserves_minus Q _ _ _ _ _ _ _ 
        CR _ _ _ _ _ _ _ _ _).
  apply (@order_preserving _ _ _ _ _
      _ (@cast Q CR _) _).
  apply eq_le. 
  autounfold with QMC.
  destruct eps. simpl.
  ring.
Qed.

(** It will only be called for [d] such that [extraSpaceX1W] is
valid, i.e.,
0 ≤ d ≤ ('tr) * leftCriticalAngle
/\ d ≤ (('Qmake 1 4)*π)
 *)
Definition approxDecideXAdmiss (d:CR) :=
approxDecLtRQ  (extraSpaceX1W ('α * d)) Xs.

(** Now compute the quality (the amount of upward shift) for a
given parameter [d]. The remaining space, which must be positive for 
admissible values, will be used up for the straighe move.
This function will only be used for admissible
[d]s -- if that simplifies anything .*)

End InverseProblem.