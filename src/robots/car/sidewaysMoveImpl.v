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
Require Import CRMisc.numericalOpt.


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

(** It seems that [d] always appears as a product with α.
  so, parametrize it over α * d *) 
Definition extraSpaceX1WValid (d:CR) : Prop :=
0 ≤ d ≤ ('tr) * leftCriticalAngle
∧ d ≤ ((' (tr * ½)) * (polarTheta βPlusBack)).

(** the srict inequality in the 
last clause is necessary, because we want 
same space to be left for the straight move,
to ensure that 
the upward is nonzero. *)
Definition dAdmissibleXwise (d:CR) :=
extraSpaceX1WValid d
∧ extraSpaceX1W ('α * d) < 'Xs.

(** we need to often compare reals. This can
 -only be done upto a finte (but arbitrary) accuracy.*)
Variable eps : Qpos.

(** It will only be called for [d] such that [extraSpaceX1W] is
valid, i.e.,
0 ≤ d ≤ ('tr) * leftCriticalAngle
/\ d ≤ (('Qmake 1 4)*π)
 *)
Definition approxDecideXAdmiss (d:CR) : bool :=
approxDecLtRQ eps (extraSpaceX1W ('α * d)) Xs.

(** Move to IRLemmasAsCR.v*)
Lemma pos_cos_CR : 
  ∀ θ : CR, 0 ≤ θ < (½ * π) → 0 < cos θ.
Proof using.
  intros ? Hbw.
  apply CRasIRless.
  eapply less_wdr; [| symmetry; apply cos_correct_CR].
  eapply less_wdl; [| symmetry; apply CRasIR0].
  rewrite CRPiBy2Correct1 in Hbw.
  rewrite <- IR_Zero_as_CR in Hbw.
  rewrite <- (CRasIRasCR_id θ) in Hbw.
  destruct Hbw as [Hbwl Hbwr].
  apply CR_lt_ltT in Hbwr.
  apply pos_cos;[ apply IR_leEq_as_CR| apply CR_less_as_IR]; assumption.
Qed.

Lemma extraSpaceX1WValidImplies : forall (d:CR),
extraSpaceX1WValid d
→
  0 ≤ 'α * d ≤ leftCriticalAngle
  ∧ 2 * 'α * d ≤ (polarTheta βPlusBack).
Proof using αPosQ.
  intros ? He.
  unfold extraSpaceX1WValid in He.
  destruct He as [Hel Her].
  destruct Hel as [Hell Helr].
  apply (order_preserving (mult ('α))) in Her.
  apply (order_preserving (mult ('α))) in Helr.
  rewrite (@simple_associativity _ _ mult _ _ _) in Helr.
  rewrite (@simple_associativity _ _ mult _ _ _) in Her.
  rewrite <- preserves_mult in Helr.
  rewrite <- preserves_mult in Her.
  rewrite (@simple_associativity _ _ mult _ _ _) in Her.
  unfold tr in Helr, Her.
  autounfold with QMC in αPosQ.
  rewrite Qmult_inv_r in Helr;[| lra].
  rewrite Qmult_inv_r in Her;[| lra].
  setoid_rewrite preserves_1 in Helr.
  rewrite mult_1_l in Helr.
  rewrite preserves_mult in Her.
  setoid_rewrite preserves_1 in Her.
  rewrite mult_1_l in Her.
  apply (order_preserving (mult ('2))) in Her.
  setoid_rewrite (@simple_associativity _ _ mult _ _ _)  in Her at 2.
  rewrite <- preserves_mult in Her.
  assert ((2 * ½) = 1) as Heq by reflexivity.
  rewrite Heq in Her.
  rewrite preserves_1 in Her.
  rewrite mult_1_l in Her.
  setoid_rewrite (@simple_associativity _ _ mult _ _ _)  in Her.
  dands; auto;[].
  apply nonneg_mult_compat; auto. apply preserves_nonneg. 
    apply lt_le. assumption.
Qed.

Require Import MCMisc.rings.
(** needed because we wish to divide by [cos (2 * 'α * d)] *)
Lemma extraSpaceX1WValidCosPos :forall  (d:CR),
extraSpaceX1WValid d
→ 0 < cos (2 * 'α * d).
Proof  using αPosQ ntriv.
  intros ? Hv.
  apply pos_cos_CR.
  apply extraSpaceX1WValidImplies in Hv.
  unfold extraSpaceX1WValid in Hv.
  rewrite <- (@simple_associativity _ _ mult _ _).
  rewrite <- (@simple_associativity _ _ mult _ _) in Hv.
  split;[apply RingLeProp3; tauto|].
  eapply le_lt_trans; [apply Hv|].
  unfold nonTrivialCarDim in ntriv.
  apply polarFirstQuadStrict; simpl;  autounfold with QMC in *; 
  simpl; try lra.
  apply lt_le in αPosQ.
  apply  Qinv_le_0_compat in αPosQ. unfold tr.
  unfold dec_recip in αPosQ.
  destruct ntriv.
  dands. remember (/ α). setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in αPosQ.
   lra.
Qed.

Section objective.

Variable d:CR.

(** Now compute the quality (the amount of upward shift) for a
given parameter [d]. The remaining space, which must be positive for 
admissible values, will be used up for the straight move.
This function will only be used for admissible
[d]s -- if that simplifies anything .

[d'] is the distance covered during the straight move
*)

Hypothesis valid : extraSpaceX1WValid d.

Let cos2αd_inv : CR.
  apply CRinv.
  exists (cos (2 * 'α * d)).
  right.
  apply extraSpaceX1WValidCosPos. (** this is opaque, so cannot use CRinvT*)
  assumption.
Defined.
  
Let d'  : CR := cos2αd_inv * ('Xs -  (extraSpaceX1W ('α * d))).

Require Import MathClasses.theory.fields.


Lemma reciperse_altL `{Field F} (x : F) Px : (// x↾Px) * x = 1.
Proof using. 
  rewrite commutativity.
  now rewrite <-(recip_inverse (x↾Px)). 
Qed.

(** there is already a ring instance decrared for CR,
 using the legacy
 definition of ring. That may cause issues.
 Remove that ring, because that needs unfolding to ugly 
legacy notations for the old [CRing].
Add the old ring declaration to a separate file, and 
import it in old files.
 *)
Add Ring tempRingCR : (stdlib_ring_theory CR).

Let sidewaysMove : list DAtomicMove 
  := SidewaysAux ('α) αNZ ('d) ('(d')).

(** the above sideways move takes up all the available space in the X direction *)
Lemma sidweaysXSpaceExact :
   extraSpaceXSidewaysCase1  α cd d d' = 'Xs.
Proof.
  unfold extraSpaceXSidewaysCase1.
  unfold d'.
  rewrite MultShuffle3r.
  unfold cos2αd_inv.
  setoid_rewrite reciperse_altL.
  unfold extraSpaceX1W.
  ring.
Qed.

Definition upwardShift : CR := d' * (sin (2 * 'α * d)).

Lemma upwardShiftCorrect: forall init,
θ2D init =0 
-> 
Y (pos2D (stateAfterAtomicMoves sidewaysMove init))
  = 
Y (pos2D init) + 'upwardShift.
Proof.
  intros ? h0.
  unfold sidewaysMove.
  rewrite SidewaysAuxState.
  unfold sidewaysDisp, upwardShift.
  simpl.
  rewrite h0.
  rewrite plus_0_l.
  autounfold with IRMC.
  simpl.
  unfold cast, Cast_instace_Q_IR, Cart_CR_IR, implCR.SinClassCR, Cart2Polar.
  autorewrite with CRtoIR.
  reflexivity.
Qed.
  
End objective.

End InverseProblem.