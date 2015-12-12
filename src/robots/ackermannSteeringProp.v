
Set Suggest Proof Using.
Require Export Coq.Program.Tactics.
Require Export LibTactics.
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

Require Import Vector.
Require Import CPS.
Require Import CPSUtils.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import CartCR.
Require Export ackermannSteering.
Require Import MCMisc.tactics.

  Add Ring RisaRing: (CRing_Ring IR).
  Add Ring cart2dir : Cart2DIRRing.

Require Export CartIR.

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.


(** 
* Characterizing the motion under Ackermann steering.

This file is highly experimental.
*)

(**width needs to be nonzero so that we can take its reciprocal in an arctan.
  others can also be required to be strictly positive*)

Definition nonTrivialCarDim (cd : CarDimensions IR) :=
  0 ≤ lengthFront cd  and  0 [<] width cd and 0 ≤ lengthBack cd.


Require Import fastReals.interface.
Require Import fastReals.misc.
Require Import geometry2D.
Require Import geometry2DProps.

  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).

Hint Unfold cos CosClassIR sin SinClassIR min MinClassIR  max MaxClassIR: IRMC.
Hint Unfold cos CosClassIR sin SinClassIR min MinClassIR  max MaxClassIR: AbstractR.

Section Proper.

  Global Instance ProperFrontUnitVec : Proper
    (equiv ==> equiv) (@frontUnitVec IR _ _).
  Proof.
    intros x y Heq. destruct x, y. apply proj2 in Heq.
    unfold frontUnitVec. simpl in *. rewrite Heq.
    reflexivity.
  Qed.

  Global Instance ProperRHSUnitVec : Proper
    (equiv ==> equiv) (@rightSideUnitVec IR _ _ _ _ _ _ _).
  Proof.
    intros x y Heq. destruct x, y. apply proj2 in Heq.
    unfold rightSideUnitVec. simpl in *. rewrite Heq.
    reflexivity.
  Qed.

  Global Instance ProperCarMinMax (cd : CarDimensions IR) : Proper
    (equiv ==> equiv) (fun r => carMinMaxXY r cd).
  Proof.
    intros x y Heq. unfold carMinMaxXY. simpl.
    unfold boundingUnion. simpl.
    unfold backLeft, frontLeft, frontRight, backRight.
    rewrite Heq. reflexivity.
  Qed.

End Proper.

(** For getting out of a parallel parked spot, a car's orientation does not
need to change by 90 degrees. Assume that the X axis represents the road.
Under such an orientation, it is easy to characterize the X Y extent of the car,
in terms of the coordinates of the four corners of the car*)
Section XYBounds.
  Variable cs :Rigid2DState IR.
  Variable cd :CarDimensions IR.

  Hypothesis nonTriv : nonTrivialCarDim cd.
  Hypothesis theta90 : 0 ≤ θ2D cs ≤ (½ * π).
  
  Lemma carBoundsAMAuxMin : 
    minCart (rightSideUnitVec cs * ' width cd) (- (rightSideUnitVec cs * ' width cd))
    = -('width cd) * {|X:= sin (θ2D cs); Y:= cos (θ2D cs)|}.
  Proof using All.
    destruct nonTriv as [a b]. destruct b as [c b].
    apply unitVecNonNeg in theta90.
    unfold unitVec in theta90.
    destruct theta90 as [x y]. simpl in x, y.
    apply less_leEq in c.
    unfold rightSideUnitVec. rewrite unitVecMinus90.
    unfold minCart. split; simpl;
    autounfold with IRMC.
    - rewrite Min_comm.
      rewrite leEq_imp_Min_is_lft;[ring|].
      rewrite <- cring_inv_mult_rht.
      apply mult_resp_leEq_rht;[| assumption].
      apply shift_leEq_rht. unfold cg_minus.
      rewrite cg_inv_inv.
      apply plus_resp_nonneg; assumption.

    - rewrite leEq_imp_Min_is_lft;[ring|].
      rewrite  cring_inv_mult_rht.
      apply inv_resp_leEq.
      rewrite <- cring_inv_mult_rht.
      apply mult_resp_leEq_rht;[| assumption].
      apply shift_leEq_rht. unfold cg_minus.
      rewrite cg_inv_inv.
      apply plus_resp_nonneg; assumption.
  Qed.

  (* only needed to replace leEq_imp_Min_is_lft by leEq_imp_Max_is_rht *)
  Lemma carBoundsAMAuxMax : 
    maxCart (rightSideUnitVec cs * ' width cd) (- (rightSideUnitVec cs * ' width cd))
    = ('width cd) * {|X:= sin (θ2D cs); Y:= cos (θ2D cs)|}.
  Proof using All.
    destruct nonTriv as [a b]. destruct b as [c b].
    apply unitVecNonNeg in theta90.
    unfold unitVec in theta90.
    destruct theta90 as [x y]. simpl in x, y.
    apply less_leEq in c.
    unfold rightSideUnitVec. rewrite unitVecMinus90.
    unfold maxCart. split; simpl;
    autounfold with IRMC.
    - rewrite Max_comm.
      rewrite leEq_imp_Max_is_rht;[ring|].
      rewrite <- cring_inv_mult_rht.
      apply mult_resp_leEq_rht;[| assumption].
      apply shift_leEq_rht. unfold cg_minus.
      rewrite cg_inv_inv.
      apply plus_resp_nonneg; assumption.

    - rewrite leEq_imp_Max_is_rht;[ring|].
      rewrite  cring_inv_mult_rht.
      apply inv_resp_leEq.
      rewrite <- cring_inv_mult_rht.
      apply mult_resp_leEq_rht;[| assumption].
      apply shift_leEq_rht. unfold cg_minus.
      rewrite cg_inv_inv.
      apply plus_resp_nonneg; assumption.
  Qed.

  Lemma carBoundsAMAuxMin2 : 
    minCart 
      ((- frontUnitVec cs * ' lengthBack cd)) 
      (frontUnitVec cs * ' lengthFront cd)
    =  -(frontUnitVec cs) * (' lengthBack cd).
  Proof using All.
    rewrite <- negate_mult_distr_l.
    rewrite negate_mult_distr_r.
    unfold frontUnitVec.
    setoid_rewrite <- sameXYNegate.
    setoid_rewrite unitVecMinDistr;[| assumption].
    fequiv.
    unfold cast, castCRCart2DCR. 
    fequiv.
    apply leEq_imp_Min_is_lft.
    apply shift_leEq_rht.
    unfold cg_minus. revert nonTriv.
    unfold nonTrivialCarDim.
    autounfold with IRMC.
    intros.
    rewrite cg_inv_inv.
      apply plus_resp_nonneg; tauto.
  Qed.

  Lemma carBoundsAMAuxMax2 : 
    maxCart 
      ((- frontUnitVec cs * ' lengthBack cd)) 
      (frontUnitVec cs * ' lengthFront cd)
    =  (frontUnitVec cs) * (' lengthFront cd).
  Proof using All.
    rewrite <- negate_mult_distr_l.
    rewrite negate_mult_distr_r.
    unfold frontUnitVec.
    setoid_rewrite <- sameXYNegate.
    setoid_rewrite unitVecMaxDistr;[| assumption].
    fequiv.
    fequiv.
    apply leEq_imp_Max_is_rht.
    apply shift_leEq_rht.
    unfold cg_minus. revert nonTriv.
    unfold nonTrivialCarDim.
    autounfold with IRMC.
    intros.
    rewrite cg_inv_inv.
      apply plus_resp_nonneg; tauto.
  Qed.
    
    
  Lemma carBoundsAMAux : carMinMaxXY cs cd =
  {|minxy := {|X:= X (backLeft cs cd); Y:= Y (backRight cs cd)|};
     maxxy := {|X:= X (frontRight cs cd); Y:= Y (frontLeft cs cd) |} |}.
  Proof using All.
  unfold carMinMaxXY.
  unfold backRight, backLeft.
  Local Opaque unitVec.
  simpl. unfold  boundingUnion.
  simpl. 
  Typeclasses eauto :=10.
  pose proof (minCartSum (pos2D cs - frontUnitVec cs * ' lengthBack cd)).
  unfold BoundingRectangle. simpl.
  Local Opaque minCart.
  Local Opaque maxCart.
  simpl. split; simpl.
  - rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).  
    rewrite (minCartSum _).
    rewrite carBoundsAMAuxMin.
    rewrite <- (@simple_associativity _ _ (@minCart IR _) _ _).
    unfold frontRight, frontLeft.
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).  
    rewrite minCartSum.
    rewrite (@commutativity _ _ _ (@minCart IR _) _ _ (rightSideUnitVec cs * ' width cd)).
    rewrite carBoundsAMAuxMin.
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite minCartSum.
    rewrite (@commutativity _ _ _ (@plus (Cart2D IR) _) _ _ 
      (-' width cd * {| X := sin (θ2D cs); Y := cos (θ2D cs) |})).
    rewrite (@commutativity _ _ _ (@plus (Cart2D IR) _) _ _ 
      (-' width cd * {| X := sin (θ2D cs); Y := cos (θ2D cs) |})).
    rewrite minCartSum. simpl.
    rewrite carBoundsAMAuxMin2.
    unfold rightSideUnitVec. rewrite unitVecMinus90.
    split; simpl; autounfold with IRMC; IRring.
  - 
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).  
      rewrite (maxCartSum _).
    rewrite carBoundsAMAuxMax.
    rewrite <- (@simple_associativity _ _ (@maxCart IR _) _ _).
    unfold frontRight, frontLeft.
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).  
    rewrite maxCartSum.
    rewrite (@commutativity _ _ _ (@maxCart IR _) _ _ (rightSideUnitVec cs * ' width cd)).
    rewrite carBoundsAMAuxMax.
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite maxCartSum.
    rewrite (@commutativity _ _ _ (@plus (Cart2D IR) _) _ _ 
      (' width cd * {| X := sin (θ2D cs); Y := cos (θ2D cs) |})).
    rewrite (@commutativity _ _ _ (@plus (Cart2D IR) _) _ _ 
      (' width cd * {| X := sin (θ2D cs); Y := cos (θ2D cs) |})).
    rewrite maxCartSum.
    rewrite carBoundsAMAuxMax2.
    unfold rightSideUnitVec. rewrite unitVecMinus90.
    split; simpl; autounfold with IRMC; IRring.
  Qed.


End XYBounds.

  (** When the turn curvature is fixed, a car's position and orientation, and hence
   the position of its corners, and hence the confining axis-aligned rectangle,
   can be defined just as a function of initial state and the car's orientation.
    The lemma [carMinMaxXYAM] below proves the correctness of this definition..
  *)
   
  Definition carMinMaxXYAtθ  (init : Rigid2DState IR) (cd : CarDimensions IR)
        (turnRadius θ : IR) : Line2D IR :=  
  let θi := θ2D init in
  '(pos2D init) +
  {| minxy:= {|
      X := turnRadius * (sin θ - sin θi) - (width cd) * sin θ - (lengthBack cd) * cos  θ;
      Y := turnRadius * (cos θi - cos θ) - (width cd) * cos θ - (lengthBack cd) * sin  θ
        |};
     maxxy := {|
      X := turnRadius * (sin θ - sin θi) + (width cd) * sin θ + (lengthFront cd) * cos  θ;
      Y := turnRadius * (cos θi - cos θ) + (width cd) * cos θ + (lengthFront cd) * sin  θ
        |}
  |}.
  
  Global Instance ProperCarMinMaxAtθ (cd : CarDimensions IR) : Proper
    (equiv ==> equiv ==> equiv ==> equiv) 
      (fun r tr θ=> carMinMaxXYAtθ r cd tr θ).
  Proof.
    intros ? ? H1e ? ? H2e ? ? H3e.
    unfold carMinMaxXYAtθ. rewrite H1e.
    rewrite H2e. rewrite H3e.
    reflexivity.
  Qed.

Section Props.
Variable maxTurnCurvature : Qpos.
Variable acs : AckermannCar maxTurnCurvature.

  
  Local Notation  "∫" := Cintegral.

(** 
We characterize the motion of a car at a particular fixed turn curvature.
The speed is not fixed, even though it seems like an enticing temporary simpilification.
The assumption that [linSpeed] is continuous makes it impossible to assume
that the car immediately achieves the desired velocity from a state of rest.
Fortunately, the lack of constanthood assumption of [linSpeed] 
does not complicate the integrals.


TODO: Ideally, we should let the turn curvature vary a bit 
(upto some epsilon) during the process.
This will SIGNIFICANTLY complicate the integrals.
*)

Section Cases.

  Variable tstart : Time.
  Variable tend : Time.

  Hypothesis tstartEnd : (tstart ≤ tend).

  Definition confinedDuring (cd :CarDimensions IR) (rect: Line2D IR) :=
   forall  (t :Time),
    tstart ≤ t ≤ tend
    → carMinMaxXY (rigidStateAtTime acs t) cd ⊆ rect.

  Local Notation θ0 := ({theta acs} tstart).
  
  (** We will consider 2 classes of motions between [tstart] and [tend]. These classes suffice for our purpose

    -1) move with fixed steering wheel ([turnCurvature])
    -2) rotate the steering wheel while remaining stationary ([linVel = 0]).

  *)

  Section FixedSteeringWheel.
  Variable tc : IR.

(* TODO: It suffices to assume it for just rational times, because of continuity *)  
  Hypothesis fixed : forall (t :Time), 
    (tstart ≤ t ≤ tend)  -> {turnCurvature acs} t = tc.

  (** [theta] at time [t] is also needed obtain position at time [t] by integration *)
  Lemma fixedSteeringTheta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
(** ib denotes the pair of numbers that goes at the bottom and at the top of ∫ *)
    let ib := @mkIntBnd _ tstart t (proj1 p) in
    ({theta acs} t - {theta acs} tstart) = tc* (∫ ib (linVel acs)).
  Proof using fixed.
    intros ? Hb ?.
    setoid_rewrite <- TBarrowScale;
      [| apply (derivRot acs)|];[reflexivity|].
    intros tb Hbb.  rewrite mult_comm.
    simpl. apply mult_wd;[| reflexivity].
    apply fixed. unfold intgBndL, intgBndR in Hbb.  simpl in Hbb.
    repnd. autounfold with IRMC. unfold Le_instance_Time.
    split; eauto 2 with CoRN.
  Qed.


  Section NoSignChange.
  (** While characterizing the space needed by a move,
    the whole trajectory matters, not just the initial and final
    positions. So, we rule out the case of the car moving both
    forward and backward during an atomic move.*)
  Hypothesis nsc : noSignChangeDuring (linVel acs) tstart tend.

  Hypothesis tcSign : (tc≤0 \/ 0≤tc).

  (** As a result, during an atomic move,
    theta is always between its initial and final value. *)
  Lemma thetaMonotone : forall (t :Time)  (p: tstart ≤ t ≤ tend),
    inBetweenR ({theta acs} t) ({theta acs} tstart) ({theta acs} tend).
  Proof using All.
    eapply nosignChangeInBw;
      [assumption | eapply derivRot |].
    apply nonSignChangeMult; try assumption.
    destruct tcSign; [right|left]; intros t Hb; rewrite fixed; auto.
  Qed.
    
  End NoSignChange.
  (** We consider the case when the front wheels are not straight, i.e. the 
      turn curvature is nonzero. The other case (front wheels are perfectly straight) is simpler, 
      but needs to be handled differently due to "divide by 0" issues during integration.*)

  Section TCNZ.
  (**Needed because [tc] shows up as a denominator
     during integration below in [fixedCurvX].*)
  Hypothesis tcNZ : (tc [#] 0).
  Local Notation turnRadius  (* :IR *) := (f_rcpcl tc tcNZ).
  
  (** [X] coordinate of the [position] at a given time. Note that in CoRN,
      division is a ternary operator. [a[/]b[//][bp]] denotes the real number [a]
      divided by the non-zero real number [b], where [bp] is the proof of non-zero-hood
      of [b].
   *)
  Lemma fixedSteeeringX : forall (t :Time) (_: tstart ≤ t ≤ tend),
    ({X (position acs)} t - {X (position acs)} tstart) =  
        ((Sin ({theta acs} t) - Sin ({theta acs} tstart)) [/] tc [//] tcNZ).
  Proof using (fixed tcNZ).
    intros  ? Hb.
    setoid_rewrite <- TBarrow with (p:= proj1 Hb);[| apply (derivX acs)].
    pose proof (@TContRDerivativeSin _ _ _ _ (derivRot acs)) as X.
    apply mult_cancel_rht with (z:=tc);[exact tcNZ|].
    rewrite div_1.
    rewrite (@mult_commut_unfolded IR).
    rewrite <- CIntegral_scale.
    match type of X with
      isIDerivativeOf ?l _ => rewrite (@Cintegral_wd2 _ _ _ _ l)
    end.
    - rewrite TBarrow;[| apply X]. fold (CFSine (theta acs)).
      rewrite CFSineAp, CFSineAp. reflexivity.
    - intros tb Hbb.
      autounfold with IRMC in Hb.
      unfold Le_instance_Time in Hb. 
      autounfold with TContRMC.
      fold (CFCos (theta acs)).
      (* autorewrite with IContRApDown. *)
      rewrite IContRMultAp,IContRMultAp,IContRMultAp,IContRMultAp, CFCosAp,IContRConstAp.
      rewrite fixed with (t:=tb); [ring |].
      autounfold with IRMC.  unfold Le_instance_Time.
      unfold inBounds in Hbb. simpl in Hbb. repnd.
      split; eauto 2 with CoRN.
  Qed.

  Lemma tcnegNZ : - tc [#] 0.
  Proof using tcNZ. 
    apply inv_resp_ap_zero. exact tcNZ.
  Qed.

  Lemma fixedSteeeringY : forall (t :Time) (_: tstart ≤ t ≤ tend),
    ({Y (position acs)} t - {Y (position acs)} tstart) =  
        ((Cos ({theta acs} tstart) - Cos ({theta acs} t)) [/] tc [//] tcNZ).
  Proof using (fixed tcNZ).
    intros  ? Hb.
    setoid_rewrite <- TBarrow with (p:= proj1 Hb);[| apply (derivY acs)].
    pose proof (@IContRDerivativeCos _ _ _ _ (derivRot acs)) as X.
    apply mult_cancel_rht with (z:=-tc);[exact tcnegNZ|].
    autounfold with IRMC.
    symmetry. rewrite cring_inv_mult_lft. symmetry.
    rewrite div_1.
    rewrite (@mult_commut_unfolded IR).
    rewrite <- CIntegral_scale.
    match type of X with
      isIDerivativeOf ?l _ => rewrite (@Cintegral_wd2 _ _ _ _ l)
    end.
    - rewrite TBarrow;[| apply X]. fold (CFCos (theta acs)).
      rewrite CFCosAp, CFCosAp. unfold cg_minus.
      autounfold with IRMC.
      ring.
    - intros tb Hbb.
      autounfold with IRMC in Hb.
      unfold Le_instance_Time in Hb. 
      autounfold with TContRMC.
      rewrite IContRMultAp,IContRMultAp,IContRMultAp,IContRMultAp, CFSineAp,IContRConstAp.
      rewrite composeIContAp.
      simpl. symmetry.
      pose proof (@pfwdef2 _ Sine ({theta acs} tb) (fst Continuous_Sin ({theta acs} tb) I) I) as Hr. 
      rewrite Hr.
      Local Transparent Sin.
      unfold Sin. simpl.
      Local Opaque Sin.
      rewrite fixed with (t:=tb); [ring |].
      autounfold with IRMC.  unfold Le_instance_Time.
      unfold inBounds in Hbb. simpl in Hbb. repnd.
      split; eauto 2 with CoRN.
  Qed.


  Lemma fixedSteeeringXY : forall (t :Time) (_: tstart ≤ t ≤ tend),
    posAtTime acs t - posAtTime acs tstart = 
      'turnRadius * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart).
  Proof using (fixed tcNZ).
    intros ? Hb.
    unfold rhsUnitVecAtTime, rightSideUnitVec, rigidStateAtTime.
    simpl. rewrite unitVecMinus90, unitVecMinus90.
    unfold posAtTime. split; simpl;
      [rewrite fixedSteeeringX by assumption| rewrite fixedSteeeringY by assumption];
    autounfold with IRMC; unfold cf_div; ring.
  Qed.

  Section XYBounds.
  Variable cd :CarDimensions IR.
  Hypothesis nonTriv : nonTrivialCarDim cd.
  Hypothesis theta90 :  forall (t :Time)  (p: tstart ≤ t ≤ tend),
     0 ≤ ({theta acs} t) ≤ (½ * π).

  (** To characterize the space required, one needs to study the motion of the corners.
      Note that [unitVec ({theta acs} t)] and [rhsUnitVecAtTime acs t] are orthogonal
      to each other at all times [t]. Also, the magnitudes in these directions are exactly
      the coordinates in the reference frame with origin at the turnCenter, and the
      [rhsUnitVecAtTime acs t] axis pointing towards the car. Hence,
      each corner is rotating around the turnCenter, as explained in 
      https://www.youtube.com/watch?v=oYMMdjbmQXc
      *)
  Lemma backRightXYAM : forall (t :Time) (Hb : tstart ≤ t ≤ tend),
    backRightAtTime acs t cd - backRightAtTime acs tstart cd =  
    '(turnRadius + width cd) * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart) -
    'lengthBack cd * (unitVec ({theta acs} t) - unitVec θ0).
  Proof using (cd fixed tcNZ).
    intros ? ?. unfold backRightAtTime,  backRight, frontUnitVec . simpl.
    fold (rhsUnitVecAtTime acs t).
    fold (rhsUnitVecAtTime acs tstart).
    match goal with
    [|- equiv ?l _] => assert 
      (l=(posAtTime acs t - posAtTime acs tstart)
          - (' lengthBack cd) * (unitVec ({theta acs} t) - unitVec θ0)
          + (' width cd) * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart))
        as Heq by ring; rewrite Heq; clear Heq
    end.

    rewrite fixedSteeeringXY by assumption.
    setoid_rewrite <- sameXYAdd. unfold cast, castCRCart2DCR.
    ring.
  Qed.

  Lemma backLeftXYAM : forall (t :Time) (Hb : tstart ≤ t ≤ tend),
    backLeftAtTime acs t cd - backLeftAtTime acs tstart cd =  
    '(turnRadius - width cd) * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart) -
    'lengthBack cd * (unitVec ({theta acs} t) - unitVec θ0).
  Proof using (cd fixed tcNZ).
    intros ? ?. unfold backLeftAtTime,  backLeft, frontUnitVec . simpl.
    fold (rhsUnitVecAtTime acs t).
    fold (rhsUnitVecAtTime acs tstart).
    match goal with
    [|- equiv ?l _] => assert 
      (l=(posAtTime acs t - posAtTime acs tstart)
          - (' lengthBack cd) * (unitVec ({theta acs} t) - unitVec θ0)
          - (' width cd) * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart))
        as Heq by ring; rewrite Heq; clear Heq
    end.

    rewrite fixedSteeeringXY by assumption.
    setoid_rewrite <- sameXYAdd. unfold cast, castCRCart2DCR.
    rewrite sameXYNegate.
    ring.
  Qed.

  Lemma frontRightXYAM : forall (t :Time) (Hb : tstart ≤ t ≤ tend),
    frontRightAtTime acs t cd - frontRightAtTime acs tstart cd =  
    '(turnRadius + width cd) * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart) 
    + 'lengthFront cd * (unitVec ({theta acs} t) - unitVec θ0).
  Proof using (cd fixed tcNZ).
    intros ? ?. unfold frontRightAtTime,  frontRight, frontUnitVec . simpl.
    fold (rhsUnitVecAtTime acs t).
    fold (rhsUnitVecAtTime acs tstart).
    match goal with
    [|- equiv ?l _] => assert 
      (l=(posAtTime acs t - posAtTime acs tstart)
          + (' lengthFront cd) * (unitVec ({theta acs} t) - unitVec θ0)
          + (' width cd) * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart))
        as Heq by ring; rewrite Heq; clear Heq
    end.

    rewrite fixedSteeeringXY by assumption.
    setoid_rewrite <- sameXYAdd. unfold cast, castCRCart2DCR.
    ring.
  Qed.

  Lemma frontLeftXYAM : forall (t :Time) (Hb : tstart ≤ t ≤ tend),
    frontLeftAtTime acs t cd - frontLeftAtTime acs tstart cd =  
    '(turnRadius - width cd) * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart) 
    + 'lengthFront cd * (unitVec ({theta acs} t) - unitVec θ0).
  Proof using (cd fixed tcNZ).
    intros ? ?. unfold frontLeftAtTime,  frontLeft, frontUnitVec . simpl.
    fold (rhsUnitVecAtTime acs t).
    fold (rhsUnitVecAtTime acs tstart).
    match goal with
    [|- equiv ?l _] => assert 
      (l=(posAtTime acs t - posAtTime acs tstart)
          + (' lengthFront cd) * (unitVec ({theta acs} t) - unitVec θ0)
          - (' width cd) * (rhsUnitVecAtTime acs t - rhsUnitVecAtTime acs tstart))
        as Heq by ring; rewrite Heq; clear Heq
    end.

    rewrite fixedSteeeringXY by assumption.
    setoid_rewrite <- sameXYAdd. unfold cast, castCRCart2DCR.
    rewrite sameXYNegate.
    ring.
  Qed.


    Require Import MCMisc.rings.

  Lemma carMinMaxXYAM : 
    forall (t :Time) (Hb : tstart ≤ t ≤ tend),
    carMinMaxXY (rigidStateAtTime acs t) cd
    = carMinMaxXYAtθ (rigidStateAtTime acs tstart) cd turnRadius ({theta acs} t).
  Proof using (fixed nonTriv tcNZ theta90).
    intros ? ?.
    rewrite carBoundsAMAux;[|assumption| apply theta90; assumption].
    Local Opaque unitVec. 
      simpl. unfold rightSideUnitVec.
      rewrite unitVecMinus90.
    Local Transparent unitVec. simpl. 
    rewrite foldPlusCart.
    rewrite (foldPlusCart ({X acs} t)).
    change ({|
          X := {X acs} t;
          Y := {Y acs} t |}) with (posAtTime acs t).
    apply fixedSteeeringXY in Hb.
    apply RingShiftMinusR in Hb.
    unfold rhsUnitVecAtTime, rightSideUnitVec in Hb.
    rewrite unitVecMinus90 in Hb.
    rewrite unitVecMinus90 in Hb.
    simpl in Hb.
    split; simpl; rewrite Hb;
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _ ); 
    fequiv;split; simpl; IRring.
  Qed.
   
  Lemma auxConfinedDuringAMIf : forall (confineRect : Line2D IR),
    noSignChangeDuring (linVel acs) tstart tend
    ->
    (∀ (θ : IR), inBetweenR θ ({theta acs} tstart) ({theta acs} tend)
           -> carMinMaxXYAtθ (rigidStateAtTime acs tstart) cd turnRadius θ ⊆ confineRect)
     ->  confinedDuring cd confineRect.
  Proof using All.
    intros ? Hn hh t Hb.
    specialize (hh ({theta acs}t)).
    rewrite carMinMaxXYAM;[|assumption].
    apply hh.
    apply thetaMonotone; try assumption.
    pose proof (fst (less_conf_ap _ _ _) tcNZ) as Hdec.
    autounfold with IRMC.
    destruct Hdec; [left|right]; eauto 2 with CoRN.
  Qed.

  End XYBounds.

  End TCNZ.
  
  End FixedSteeringWheel.
  



  Section LinVel0.
  (** Now consider the second case where the steering wheel may move, but the car remains stationary *)
    Hypothesis lv0 :  forall (t :Time), 
      (tstart ≤ t ≤ tend)  -> {linVel acs} t = 0.

    Lemma LV0Theta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
        {theta acs} t = {theta acs} tstart.
    Proof using lv0.
      intros. eapply TDerivativeEq0;[tauto | apply derivRot|].
      intros tt Hb. simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.

 Local Opaque FCos.
    Lemma LV0X : forall (t :Time) (p: tstart ≤ t ≤ tend),
      {X (position acs)} t = {X (position acs)} tstart .
    Proof using lv0.
      intros. eapply TDerivativeEq0;[tauto | apply derivX|].
      intros tt Hb.
      simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.

    Lemma LV0Y : forall (t :Time) (p: tstart ≤ t ≤ tend),
      {Y (position acs)} t = {Y (position acs)} tstart .
    Proof using lv0.
      intros. eapply TDerivativeEq0;[tauto | apply derivY|].
      intros tt Hb.
      simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.

    Lemma LV0 : forall (t :Time) (p: tstart ≤ t ≤ tend),
      rigidStateAtTime acs t = rigidStateAtTime acs tstart.
    Proof using lv0.
      intros. split;[split|]; simpl;
      eauto using LV0Theta, LV0X, LV0Y.
    Qed.

  End LinVel0.
  
(* TODO : given the car's dimensions, confine the whole car within 
  a "small, yet simple" region
  during the above motion. *)

End Cases.

Section AtomicMove.
(** * Atomic Move

We will build complex manueuvers out of the following basic move :
turn the steering wheel so that the turnCurvature has a particular value ([tc]),
and then drive for a particular distance ([distance]).
Note that both [tc] and [distance] are signed -- the turn center can be on the either side,
and one can drive both forward and backward *)
  Record AtomicMove := mkAtomicMove
  {
     am_distance : IR;
     am_tc : IR
  }.

  (** Needed because equality on reals (IR) is different 
      from syntactic equality 
      ([≡]). *)
      
  Global Instance Equiv_AtomicMove : Equiv AtomicMove :=
    fun (ml mr : AtomicMove) => (am_distance ml = am_distance mr) 
          /\ (am_tc ml = am_tc mr).

  (** To make tactics like [reflexivity] work, we needs to show
  that the above defined custom defined equality on [AtomicMove] 
  is an equivalence relation.*)
  Global Instance Equivalence_instance_AtomicMove 
    : @Equivalence (AtomicMove) equiv.
 Proof using .
  unfold equiv, Equiv_AtomicMove. split.
  - intros x. destruct x. simpl. split; auto with *.
  - intros x y. destruct x,y. simpl. intros Hd; destruct Hd;
      split; auto with relations.

  - intros x y z. destruct x,y,z. simpl. intros H0 H1.
    repnd.
    split; eauto 10
    with relations.
  Qed.

  Variable am : AtomicMove.
  Definition amTurn := (am_tc am) [#] 0.
  Definition amNoTurn := (am_tc am) = 0.
  
  Variable tstart : Time.
  Variable tend : Time.
  

  Set Implicit Arguments.
  (** This defines what it means for the car's controls to follow the atomic move [am] during time [tstart] to [tend] *)
  Record CarExecutesAtomicMoveDuring (p: tstart < tend) : Type :=
  {
    am_tdrive : Time;

    (**strict inequalities prevents impossilities like covering non-zero distance in 0 time.
      Note that [linVel] and [turnCurvature] evolve continuously.
     *)
    am_timeInc : (tstart < am_tdrive < tend);
 
    am_steeringControls : ({turnCurvature acs} am_tdrive) = (am_tc am) 
      /\ forall (t:Time), (tstart ≤ t ≤ am_tdrive) 
          -> {linVel acs} t = 0;

 
  (** From time [tdrive] to [tend], the steering wheel is held fixed*)
    am_driveControls : forall (t:Time), (am_tdrive ≤ t ≤ tend) 
          ->  {turnCurvature acs} t = {turnCurvature acs} am_tdrive;
          
  (** From time [tsteer] to [drive], the steerring wheel rotates to attain a configuration 
    with turn curvature [tc]. The brakes are firmly placed pressed.*)
   am_driveDistance : 
      let pf := (timeLtWeaken (proj2 (am_timeInc))) in 
      let driveIb := (@mkIntBnd _ am_tdrive tend pf) in 
          (am_distance am) = ∫ driveIb (linVel acs)
  }.

  Definition CarMonotonicallyExecsAtomicMoveDuring (p: tstart < tend) : Type :=
    CarExecutesAtomicMoveDuring p
    and (noSignChangeDuring (linVel acs) tstart tend). 
  
  Hypothesis pr : tstart < tend.
  
  (** Now, we assume that the car executes the atomic move [am] from [tstart] to [tend],
    and characterize the position and orientation at [tend], in terms of their values at [tstart]. *)
  Hypothesis amc : CarExecutesAtomicMoveDuring pr.
  
  Local Notation tc := (am_tc am).
  Local Notation distance := (am_distance am).
  Local Notation tdrive := (am_tdrive amc).
  
  Lemma am_timeIncWeaken : (tstart ≤ tdrive ≤ tend).
  Proof using Type.
    pose proof (am_timeInc amc).
    split; apply timeLtWeaken; tauto.
  Qed.

  Local Notation timeInc := am_timeIncWeaken.
  Ltac timeReasoning :=
    autounfold with IRMC; unfold Le_instance_Time;
      destruct timeInc; eauto 2 with CoRN; fail.

  Lemma am_timeStartEnd : (tstart  ≤ tend).
  Proof using All.
    pose proof (am_timeIncWeaken).
    repnd.  timeReasoning.
  Qed.

   Lemma am_driveDistanceFull : 
      let driveIb := (@mkIntBnd _ tstart tend am_timeStartEnd) in 
          (am_distance am) = ∫ driveIb (linVel acs).
   Proof using Type.
    simpl. 
    rewrite CintegralSplit 
      with (pl:= proj1 am_timeIncWeaken)
           (pr:= proj2 am_timeIncWeaken).
    pose proof (am_steeringControls amc) as steeringControls.
    apply proj2 in steeringControls.
    rewrite (@Cintegral_wd2  _ _ _ _ [0]).
    Focus 2.
      intros x Hb. simpl. destruct Hb as [Hbl Hbr].
      simpl in Hbl, Hbr. apply steeringControls.
      split; timeReasoning.
    rewrite CintegralZero.
    autounfold with IRMC.
    ring_simplify.
    rewrite (am_driveDistance).
    apply Cintegral_wd;[| reflexivity].
    simpl. split;
    reflexivity.
  Qed.

  Local Notation θs := ({theta acs} tstart).
  Local Notation Xs := ({X (position acs)} tstart).
  Local Notation Ys := ({Y (position acs)} tstart).
  Local Notation Ps := (posAtTime acs tstart).


  Lemma AtomicMoveθ : {theta acs} tend =  θs + tc * distance.
  Proof using All.
    pose proof (am_driveControls amc) as driveControls.
    eapply  fixedSteeringTheta with (t:= tend) in driveControls.
    Unshelve. Focus 2. timeReasoning.
    simpl in driveControls.
    rewrite Cintegral_wd in driveControls;[| | reflexivity].
    Focus 2. instantiate (1 := let pf := (timeLtWeaken (proj2 (am_timeInc amc))) in 
                (@mkIntBnd _ tdrive tend pf)).
     simpl. split; reflexivity; fail.
    pose proof (am_steeringControls amc) as steeringControls.
    rewrite (proj1 steeringControls) in driveControls.
    rewrite (fun p => LV0Theta tstart tdrive p tdrive) in driveControls;[| apply (proj2 steeringControls) 
        | timeReasoning ].
    rewrite <- (am_driveDistance amc) in driveControls.
    rewrite <- driveControls. simpl.
    autounfold with IRMC. simpl. ring. 
  Qed.

  Lemma rigidStateNoChange : forall t:Time, 
    tstart ≤ t ≤ tdrive
    -> (rigidStateAtTime acs t) = (rigidStateAtTime acs tstart).
  Proof using Type.
    apply LV0. destruct amc.
    simpl in *.
    tauto.
  Qed.

  (** 2 cases, based on whether the steering wheel is perfectly straight before driving.
    To avoid a  divide-by-0, the integration has to be done differently in these cases. *)
  Section TCNZ.
  Hypothesis (tcNZ : amTurn).
  
    Lemma AtomicMoveXT : {X (position acs)} tend =  Xs +
          ((Sin ({theta acs} tend) - Sin θs) [/] tc [//] tcNZ).
    Proof using All.
      pose proof (am_driveControls amc) as driveControlsb.
      pose proof (am_steeringControls amc) as steeringControls.
      setoid_rewrite (proj1 steeringControls) in driveControlsb.
      eapply  fixedSteeeringX with (t:= tend) (tcNZ:=tcNZ) in driveControlsb.
      Unshelve. Focus 2. timeReasoning.
      unfold cf_div in driveControlsb.
      rewrite (fun p => LV0X tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      rewrite (fun p => LV0Theta tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      setoid_rewrite <- driveControlsb. simpl. autounfold with IRMC. simpl. ring.
    Qed.

    Lemma AtomicMoveX : {X (position acs)} tend =  Xs +
          ((Sin (θs + tc * distance) - Sin θs) [/] tc [//] tcNZ).
    Proof using All.
      unfold cf_div. rewrite <- AtomicMoveθ.
      exact AtomicMoveXT.
    Qed.

    Lemma AtomicMoveYT : {Y (position acs)} tend =  Ys +
          ((Cos θs - Cos ({theta acs} tend)) [/] tc [//] tcNZ).
    Proof using All.
      pose proof (am_driveControls amc) as driveControlsb.
      pose proof (am_steeringControls amc) as steeringControls.
      setoid_rewrite (proj1 steeringControls) in driveControlsb.
      eapply  fixedSteeeringY with (t:= tend) (tcNZ:=tcNZ) in driveControlsb.
      Unshelve. Focus 2. timeReasoning.
      unfold cf_div in driveControlsb.
      rewrite (fun p => LV0Y tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      rewrite (fun p => LV0Theta tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      setoid_rewrite <- driveControlsb. simpl. autounfold with IRMC. simpl. ring.
    Qed.


    Lemma AtomicMoveY : {Y (position acs)} tend =  Ys +
          ((Cos θs - Cos (θs + tc * distance)) [/] tc [//] tcNZ).
    Proof using All.
      unfold cf_div. rewrite <- AtomicMoveθ.
      exact AtomicMoveYT.
    Qed.

    Lemma AtomicMoveXYT : posAtTime acs tend =  Ps +
         {|X:=(Sin ({theta acs} tend) - Sin θs);
             Y:=(Cos θs - Cos ({theta acs} tend))|} 
      * '(f_rcpcl tc  tcNZ).
    Proof using All.
      split; simpl;[apply AtomicMoveXT | apply AtomicMoveYT].
    Qed.

    Lemma AtomicMoveXY : posAtTime acs tend =  Ps +
         {|X:=(Sin (θs + tc * distance) - Sin θs);
             Y:=(Cos θs - Cos (θs + tc * distance))|} 
      * '(f_rcpcl tc  tcNZ).
    Proof using All.
      split; simpl;[apply AtomicMoveX | apply AtomicMoveY].
    Qed.

  Require Import CoRN.logic.Stability.

    Section XYBounds.
    Variable cd :CarDimensions IR.
    Hypothesis nonTriv : nonTrivialCarDim cd.
    Hypothesis theta90 :  forall (t :Time)  (p: tstart ≤ t ≤ tend),
     0 ≤ ({theta acs} t) ≤ (½ * π).

    Local Notation turnRadius  (* :IR *) := (f_rcpcl tc tcNZ).

  Lemma noSignChangeDuringWeaken: forall F a1 b1 a2 b2,
    noSignChangeDuring F a1 b1
    -> a1 ≤ a2
    -> b2 ≤ b1
    -> noSignChangeDuring F a2 b2.
  Proof using .
    intros ? ? ? ? ? Hn ? ?. destruct Hn as [Hn | Hn];[left|right];
      intros t Hb; apply Hn; destruct Hb; split; eauto 2 with CoRN.
  Qed.
    Ltac dimp H :=
    lapply H;[clear H; intro H|].

  Lemma AMTurnCurvature : ∀ t : Time,
      tdrive ≤ t ≤ tend → {turnCurvature acs} t = tc.
  Proof using Type.
    destruct amc. simpl in *.
    apply proj1 in am_steeringControls0.
    setoid_rewrite am_steeringControls0 
        in am_driveControls0.
    assumption.
  Qed.

   Hypothesis nosign : noSignChangeDuring (linVel acs) tstart tend.
    
    (*Local*) Lemma confinedDuringTurningAMIfAux : forall (confineRect : Line2D IR),
    (∀ (θ : IR), inBetweenR θ ({theta acs} tstart) ({theta acs} tend)
           -> carMinMaxXYAtθ (rigidStateAtTime acs tstart) cd turnRadius θ ⊆ confineRect)
     ->  confinedDuring tdrive tend cd confineRect.
    Proof using All.
      intros ? Hb.
      eapply noSignChangeDuringWeaken in nosign;
        [ |  exact (proj1 am_timeIncWeaken)
        | apply leEq_reflexive].
      destruct am_timeIncWeaken.
      pose proof (rigidStateNoChange tdrive) as XX.
      dimp XX;[|split;auto].
      eapply auxConfinedDuringAMIf with (tcNZ:=tcNZ); eauto.
      - apply AMTurnCurvature.
      - intros. apply theta90. repnd. split; 
            autounfold with IRMC; eauto 2 with CoRN.
      - intros ? Hj.

      assert (carMinMaxXYAtθ (rigidStateAtTime acs tdrive) cd
        turnRadius θ= 
      carMinMaxXYAtθ (rigidStateAtTime acs tstart) cd
        turnRadius θ
      ) as HH. apply ProperCarMinMaxAtθ; auto.
      rewrite HH.
      apply Hb. clear Hb.
      unfold inBetweenR in Hj. apply proj2 in XX.
      simpl in XX.
      rewrite  XX in Hj. exact Hj.
    Qed.

  Definition confinedTurningAM  (init : Rigid2DState IR) 
        (confineRect : Line2D IR) :=
    let θi := (θ2D init) in
    let θf := θi + tc * distance in
    ∀ (θ : IR), 
      inBetweenR θ θi θf
           -> carMinMaxXYAtθ init cd turnRadius θ ⊆ confineRect.
           
  Lemma confinedTurningAMCorrect : forall (confineRect : Line2D IR),
    confinedTurningAM (rigidStateAtTime acs tstart) confineRect
     ->  confinedDuring tstart tend cd confineRect.
  Proof using All.
    intros ?  hh t Hb.
    eapply stable. 
      Unshelve. Focus 2. apply StableSubsetLine2D.
           apply StableLeIR;fail.
    pose proof (leEq_or_leEq _ t tdrive) as Hd.
    eapply DN_fmap;[exact Hd|]. clear Hd. intro Hd.
    unfold confinedTurningAM in hh. simpl in hh.
    unfold inBetweenR in hh.
    setoid_rewrite <- AtomicMoveθ in hh.
    destruct Hd as [Hd | Hd].
    - apply confinedDuringTurningAMIfAux in hh.
      assert (carMinMaxXY (rigidStateAtTime acs t) cd
      = carMinMaxXY (rigidStateAtTime acs tdrive) cd
      ) as XX. 
      + apply ProperCarMinMax.
        transitivity (rigidStateAtTime acs tstart);
          [| symmetry]; 
        apply rigidStateNoChange; repnd; split; auto.
        apply am_timeIncWeaken.
      + rewrite XX. apply hh. split; auto; 
          apply am_timeIncWeaken.
    - apply confinedDuringTurningAMIfAux; auto.
      repnd; split; auto.
  Qed.

  End XYBounds.
  End TCNZ.
              
  Section TCZ.
  Hypothesis (tcZ : amNoTurn).
  
    Lemma AtomicMoveZθ : forall t:Time, tstart ≤ t ≤ tend
    -> {theta acs} t =  θs.
    Proof using All.
      intros ? Hb. eapply TDerivativeEq0;[tauto | apply derivRot|].
      intros tt Hbb.
      apply not_ap_imp_eq.
      pose proof (leEq_or_leEq _ tt tdrive) as Hd.
      intro Hc.
      apply Hd.
      clear Hd. intro Hd.
      apply ap_tight in Hc;[contradiction|]. clear H Hc.
      simpl.
      pose proof (am_steeringControls amc) as steeringControls.
      pose proof (am_driveControls amc) as driveControls.
      destruct Hd as [Hd | Hd].
      - rewrite (proj2 steeringControls);[  IRring | ]. 
        repnd. split; timeReasoning.
      - unfold amNoTurn in tcZ. rewrite (driveControls);
         [rewrite (proj1 steeringControls), tcZ; IRring | ]. 
         repnd. split; timeReasoning.
    Qed.

    Lemma AtomicMoveZX : forall (t:Time) (pl : tstart ≤ t) (pr : t ≤ tend), 
    {X (position acs)} t =  Xs
     +  (∫ (mkIntBnd pl) (linVel acs)) * (Cos θs).
    Proof using All. 
      intros ? ? ?.
      apply leftShiftEqIR.
      rewrite mult_comm.
      eapply TBarrowScale with (ib := (mkIntBnd pl));
        [apply derivX | ].
      intros tt Hb. unfold mkIntBnd, intgBndL, intgBndR in Hb. simpl in Hb.
      rewrite mult_comm at 1.
      autounfold with TContRMC.
      rewrite IContRMultAp.
      rewrite CFCosAp.
      apply mult_wd;[| reflexivity].
      apply Cos_wd.
      apply AtomicMoveZθ.
      autounfold with IRMC. repnd;
      split; eauto 3 with CoRN.
   Qed.

    Lemma AtomicMoveZY : forall (t:Time) (pl : tstart ≤ t) (pr : t ≤ tend),
    {Y (position acs)} t =  Ys
     +  (∫ (mkIntBnd pl) (linVel acs)) * (Sin θs).
    Proof using All.
      intros ? ? ?.
      apply leftShiftEqIR.
      rewrite mult_comm.
      eapply TBarrowScale with (ib := (mkIntBnd pl));
        [apply derivY | ].
      intros tt Hb. unfold mkIntBnd, intgBndL, intgBndR in Hb. simpl in Hb.
      rewrite mult_comm at 1.
      autounfold with TContRMC.
      rewrite IContRMultAp.
      rewrite CFSineAp.
      apply mult_wd;[| reflexivity].
      apply Sin_wd.
      apply AtomicMoveZθ. 
      autounfold with IRMC. repnd;
      split; eauto 3 with CoRN.
    Qed.

    Lemma AtomicMoveZ : ∀ (t:Time) 
        (pl : tstart ≤ t) (pr : t ≤ tend), 
    posAtTime acs t =
    Ps + ' ∫ ((mkIntBnd pl)) (linVel acs) * (unitVec θs).
    Proof using All.
     split; simpl; [apply AtomicMoveZX | apply AtomicMoveZY];
     auto.
    Qed.

   Lemma AtomicMoveZFinal : {theta acs} tend =  θs /\
     posAtTime acs tend =
     Ps + ('distance) * (unitVec θs).
   Proof using All.
     split;[apply AtomicMoveZθ;split; timeReasoning|].
      rewrite  (am_driveDistanceFull).
     apply AtomicMoveZ. auto.
   Qed.

   Section XYBounds.
   Variable cd :CarDimensions IR.


(* RHS was automatically obtained *)
Lemma carMinMaxAtTEq : forall t, 
carMinMaxAtT acs cd t = 
'(posAtTime acs t) +
({|
lstart := minCart
            (minCart
               (minCart
                  (-
                   frontUnitVec (rigidStateAtTime acs t) *
                   ' lengthBack cd +
                   rightSideUnitVec
                     (rigidStateAtTime acs t) *
                   ' width cd)
                  (-
                   frontUnitVec (rigidStateAtTime acs t) *
                   ' lengthBack cd -
                   rightSideUnitVec
                     (rigidStateAtTime acs t) *
                   ' width cd))
               (frontUnitVec (rigidStateAtTime acs t) *
                ' lengthFront cd -
                rightSideUnitVec
                  (rigidStateAtTime acs t) * 
                ' width cd))
            (frontUnitVec (rigidStateAtTime acs t) *
             ' lengthFront cd +
             rightSideUnitVec (rigidStateAtTime acs t) *
             ' width cd);
lend := maxCart
          (maxCart
             (maxCart
                (- frontUnitVec (rigidStateAtTime acs t) *
                 ' lengthBack cd +
                 rightSideUnitVec
                   (rigidStateAtTime acs t) * 
                 ' width cd)
                (- frontUnitVec (rigidStateAtTime acs t) *
                 ' lengthBack cd -
                 rightSideUnitVec
                   (rigidStateAtTime acs t) * 
                 ' width cd))
             (frontUnitVec (rigidStateAtTime acs t) *
              ' lengthFront cd -
              rightSideUnitVec (rigidStateAtTime acs t) *
              ' width cd))
          (frontUnitVec (rigidStateAtTime acs t) *
           ' lengthFront cd +
           rightSideUnitVec (rigidStateAtTime acs t) *
           ' width cd) |}).
Proof using Type.
    intros ?.
    hideRight.
    unfold carMinMaxAtT, carMinMaxXY. simpl.
    unfold boundingUnion. simpl.
    unfold backRight, backLeft.
    rewrite maxCartSum, minCartSum.
    unfold frontLeft.
    rewrite maxCartSum, minCartSum.
    unfold frontRight.
    rewrite maxCartSum, minCartSum.
    subst l.
    reflexivity.
Qed.
  

    
   Lemma straightAMMinMaxXY : ∀ (t:Time) 
    (pl : tstart ≤ t) (pr : t ≤ tend), 
    carMinMaxAtT acs cd t =
    carMinMaxAtT acs cd tstart 
      + '(' ∫ ((mkIntBnd pl)) (linVel acs) * (unitVec θs)).
   Proof using All.
    intros ? ? ?.
    rewrite carMinMaxAtTEq.
    rewrite carMinMaxAtTEq.
    unfold frontUnitVec, rightSideUnitVec.
    simpl θ2D. hideRight.
    rewrite AtomicMoveZθ; [|auto].
    rewrite AtomicMoveZ with (pl:=pl); [|auto].
    remember ('∫ (mkIntBnd pl) (linVel acs) * unitVec θs) as y.
    clear Heqy.
    match goal with
    [ |- _ + ?bb = _] => remember bb as l
    end.
    clear Heql.
    subst b.
    split; simpl; ring.
  Qed.

  Require Import MathClasses.orders.rings.
  Require Import MathClasses.interfaces.orders.

  (*Move: not intuitive at all, but turns out to be true,
      and exactly what is needed in the next lemma*)
  Lemma MinMax0Mult: forall (a b k:ℝ),
      Min 0 a ≤ b ≤ Max 0 a
      -> Min 0 (a*k) ≤ b*k ≤ Max 0 (a*k).
  Proof using .
    intros ? ? ? Hm.
    eapply stable.
    Unshelve. Focus 2. apply stable_conjunction; 
        apply StableLeIR; fail. 
    pose proof (leEq_or_leEq _ k 0) as Hd.
    eapply DN_fmap;[exact Hd|]. clear Hd. intro Hd.
    destruct Hd as [Hd | Hd].
    - rewrite (@commutativity _ _ _ mult _).
      rewrite (@commutativity _ _ _ mult _ b). 
      rewrite <- negate_mult_negate.
      rewrite <- (negate_mult_negate k).
      apply flip_le_negate in Hd. rewrite negate_0 in Hd.
      assert (0 = (-k) * 0) as Xr by IRring.
      rewrite Xr. clear Xr.
      setoid_rewrite MinMultLeft;[| assumption].
      setoid_rewrite MaxMultLeft;[| assumption].
      split;
      apply mult_resp_leEq_lft; auto; clear dependent k;
      apply flip_le_negate;
      setoid_rewrite negate_involutive.
      + setoid_rewrite negate_0. tauto.
      + apply proj1 in Hm. rewrite <- negate_0.
        exact Hm.

    - rewrite (@commutativity _ _ _ mult _). 
      assert (0 = k * 0) as Xr by IRring.
      rewrite Xr. clear Xr.
      setoid_rewrite MinMultLeft;[| assumption].
      setoid_rewrite MaxMultLeft;[| assumption].
      rewrite (@commutativity _ _ _ mult _).
      repnd.
      split; apply mult_resp_leEq_lft; auto.
  Qed.
   
  (** When the car is moving straight (not turning), the 
      space needed (as a  rectangle) is the union
      of the initial bouding rectangle and the final
      bounding rectangle. Unlike while turning, the whole
      trajectory need not be considered
  *)
   Definition straightAMSpaceRequirement 
      (init : Rigid2DState IR) : Line2D IR :=
      let bi := carMinMaxXY init cd in
      let bf := bi + '(('distance) * (unitVec (θ2D init))) in
          (boundingUnion bi bf).
          
   Lemma straightAMSpaceRequirementCorrect :
      noSignChangeDuring (linVel acs) tstart tend
      -> confinedDuring tstart tend cd 
          (straightAMSpaceRequirement 
                (rigidStateAtTime acs tstart)).
   Proof using All.
     unfold straightAMSpaceRequirement. 
     intros Hn t Hb.
     fold (carMinMaxAtT acs cd t).
     fold (carMinMaxAtT acs cd tstart).
     destruct Hb as [pl prr].
     rewrite straightAMMinMaxXY with (pl:=pl);[| tauto].
     unfold boundingUnion.
     assert ((minxy (carMinMaxAtT acs cd tstart)) 
        = (minxy (carMinMaxAtT acs cd tstart)) + 0) as H0 by ring.
     rewrite H0. clear H0.
     assert ((maxxy (carMinMaxAtT acs cd tstart)) 
        = (maxxy (carMinMaxAtT acs cd tstart)) + 0) as H0 by ring.
     rewrite H0. clear H0.
     setoid_rewrite  minCartSum.
     setoid_rewrite  maxCartSum.
     rewrite foldPlusLine.
     replace {|
        lstart := minxy (carMinMaxAtT acs cd tstart);
        lend := maxxy (carMinMaxAtT acs cd tstart) |}
        with  (carMinMaxAtT acs cd tstart);[| reflexivity].
     simpl.
     apply order_preserving; eauto with
      typeclass_instances.
     remember (∫ (mkIntBnd pl) (linVel acs)) as dist.
     eapply nosignChangeInBwInt with (pl:=pl)
        (Hab := am_timeStartEnd) in Hn;[| assumption].
     unfold inBetweenR in Hn.
     rewrite <- am_driveDistanceFull in Hn.
     rewrite <- Heqdist in Hn. clear Heqdist.
     pose proof Hn as Hns.
     eapply MinMax0Mult with (k:= cos θs)in Hn.
     eapply MinMax0Mult with (k:= sin θs)in Hns.
     repnd.     
     split; split; simpl; tauto.
    Qed.
  End XYBounds.
  End TCZ.

End AtomicMove.

Section AtomicMoveSpaceRequirement.

Definition AtomicMoveSign (am : AtomicMove) : Type :=
  (am_tc am =0) or (am_tc am[#]0).
  
(** combine the sufficient conditions on space required,
    both for the cases of turning and driving straignt*)
Definition carConfinedDuringAM 
  (cd : CarDimensions IR)
  (am : AtomicMove)
  (s : AtomicMoveSign am) 
  (init : Rigid2DState IR)
  (rect : Line2D IR) := 
match s with
| inl _ => (straightAMSpaceRequirement am cd init) ⊆ rect
| inr turn => (confinedTurningAM am turn cd init rect)
end.

Lemma carConfinedDuringAMCorrect:  forall 
  (cd : CarDimensions IR)
  (_ : nonTrivialCarDim cd)
  (am : AtomicMove)
  (s : AtomicMoveSign am) 
  (rect : Line2D IR)
  (tstart tend :Time)
  (p: tstart < tend)
  (_ :∀ t : Time,
     tstart ≤ t ≤ tend → 0 ≤ {theta acs} t ≤ ½ * π),
  @CarMonotonicallyExecsAtomicMoveDuring am tstart tend p
  -> @carConfinedDuringAM cd am s (rigidStateAtTime acs tstart) rect
  -> confinedDuring tstart tend cd rect.
Proof using Type.
  intros ? ? ? ? ? ? ? ? ? Ham Hcc.
  destruct Ham as [Ham Hnosign].
  destruct s as [s | s]; simpl in Hcc.
  - eapply straightAMSpaceRequirementCorrect with (cd:=cd) in Ham;      eauto.
    intros t Hb. specialize (Ham t Hb).
    eauto 2 with relations.
  - eapply confinedTurningAMCorrect in Hcc; eauto.
Qed. 

End AtomicMoveSpaceRequirement.


  Lemma CarExecutesAtomicMoveDuring_wd :
  forall ml mr tstartl tstartr tendl tendr 
      (pl :tstartl < tendl) (pr :tstartr < tendr),
    tstartl = tstartr
    -> tendl = tendr
    -> CarExecutesAtomicMoveDuring ml pl
    -> ml = mr
    -> CarExecutesAtomicMoveDuring mr pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?  tl tr Hl Heq.
    destruct Hl.
    rewrite (proj2 Heq) in  am_steeringControls0.
    simpl in am_driveDistance0.
    setoid_rewrite tl in am_steeringControls0.
    setoid_rewrite tr in am_driveControls0 .
    setoid_rewrite (proj1 Heq) in am_driveDistance0.
   econstructor; eauto. simpl.
   rewrite am_driveDistance0.
   apply Cintegral_wd;[| reflexivity].
   simpl. rewrite tr.
   split; reflexivity.
   Unshelve.
   rewrite <- tl.
   rewrite <- tr. assumption.
  Qed.

     
  Lemma CarMonotonicallyExecsAtomicMoveDuring_wd:
  forall ml mr tstartl tstartr tendl tendr 
      (pl :tstartl < tendl) (pr :tstartr < tendr),
    tstartl = tstartr
    -> tendl = tendr
    -> CarMonotonicallyExecsAtomicMoveDuring ml pl
    -> ml = mr
    -> CarMonotonicallyExecsAtomicMoveDuring mr pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?  tl tr Hl Heq.
    destruct Hl as [c Hl].
    split;[eapply CarExecutesAtomicMoveDuring_wd;eauto |].
    clear c. rewrite <- tl, <- tr. exact Hl.
  Qed.
  
  
  Lemma CarExecutesAtomicMoveDuring_wdtl :
  forall m tstartl tstartr tend 
      (pl :tstartl < tend) (pr :tstartr < tend),
    tstartl = tstartr
    -> CarExecutesAtomicMoveDuring m pl
    -> CarExecutesAtomicMoveDuring m pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?. eapply CarExecutesAtomicMoveDuring_wd; eauto; reflexivity.
  Qed.

  Lemma CarExecutesAtomicMoveDuring_wdtr :
  forall m tstart tendl tendr 
      (pl :tstart < tendl) (pr :tstart < tendr),
    tendl = tendr
    -> CarExecutesAtomicMoveDuring m pl
    -> CarExecutesAtomicMoveDuring m pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?. eapply CarExecutesAtomicMoveDuring_wd; eauto; reflexivity.
  Qed.

  Lemma CarMonotonicallyExecsAtomicMoveDuring_wdtr :
  forall m tstart tendl tendr 
      (pl :tstart < tendl) (pr :tstart < tendr),
    tendl = tendr
    -> CarMonotonicallyExecsAtomicMoveDuring m pl
    -> CarMonotonicallyExecsAtomicMoveDuring m pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?. eapply CarMonotonicallyExecsAtomicMoveDuring_wd; eauto; reflexivity.
  Qed.


(** * Executing a sequence of atomic moves *)
  Definition AtomicMoves := list AtomicMove.
  


  Inductive executesMultipleMovesDuring 
    (execSingleMoveDuring : AtomicMove → ∀ tstart tend : Time, tstart < tend → Type)
    : AtomicMoves -> forall (tstart tend : Time),  (tstart ≤ tend) -> Prop :=
  | amscNil : forall (tl tr:Time) (pe : tl = tr)(p: tl≤tr), 
        executesMultipleMovesDuring execSingleMoveDuring [] tl tr p
  | amscCons : forall (tstart tmid tend:Time) (pl : tstart < tmid) (pr : tmid ≤ tend) (p : tstart ≤ tend)
      (h: AtomicMove) (tl : AtomicMoves), 
      @execSingleMoveDuring h tstart tmid pl
      -> executesMultipleMovesDuring execSingleMoveDuring tl tmid tend pr
      -> executesMultipleMovesDuring execSingleMoveDuring(h::tl) tstart tend p.

  
  (** This predicate defines what it means for a car to follow 
    a list of atomic moves from time [tstart] to [tend].*)
  Definition CarExecutesAtomicMovesDuring :=
    executesMultipleMovesDuring CarExecutesAtomicMoveDuring.

  Definition CarMonotonicallyExecsAtomicMovesDuring :=
    executesMultipleMovesDuring CarMonotonicallyExecsAtomicMoveDuring.

Ltac substAtomicMoves amscrrl :=
    let pll := fresh "pll" in 
    let Hf := fresh "Hf" in 
    match type of amscrrl with
    ?l = _ => match goal with
        [  amscrl: @CarExecutesAtomicMoveDuring _ _ l ?pl0 |- _]
        =>
    pose proof pl0 as pll;
    rewrite amscrrl in pll;
    pose proof (@CarExecutesAtomicMoveDuring_wdtr _ _ _ _ 
      pl0 pll amscrrl amscrl) as Hf; clear dependent l
      end
      end.

Ltac substAtomicMovesMon amscrrl :=
    let pll := fresh "pll" in 
    let Hf := fresh "Hf" in 
    match type of amscrrl with
    ?l = _ => match goal with
        [  amscrl: @CarMonotonicallyExecsAtomicMoveDuring _ _ l ?pl0 |- _]
        =>
    pose proof pl0 as pll;
    rewrite amscrrl in pll;
    pose proof (@CarMonotonicallyExecsAtomicMoveDuring_wdtr _ _ _ _ 
      pl0 pll amscrrl amscrl) as Hf; clear dependent l
      end
      end.

Ltac invertAtomicMoves :=
  (repeat match goal with
    [ H: CarExecutesAtomicMovesDuring _ _ _ _ |- _] =>
      unfold CarExecutesAtomicMovesDuring in H
   | [ H: CarMonotonicallyExecsAtomicMovesDuring _ _ _ _ |- _] =>
      unfold CarMonotonicallyExecsAtomicMovesDuring in H
   | [ H: executesMultipleMovesDuring _ _ _ _ _ |- _] =>
      let Hl := fresh H "l" in
      let Hr := fresh H "r" in
      let pl := fresh H "pl" in
      let pr := fresh H "pr" in
      (inverts H as Hl Hr pl pr;[]);
      try  substAtomicMoves Hl;
      try  substAtomicMovesMon Hl
  (* invert only if only 1 case results. o/w inf. loop will result if there are fvars*)
  end);
  repeat match goal with
    [ H: eq ?x ?x |- _] => clear H
    | [ H: le ?x ?x |- _] => clear H
  end.
  
  (*
  Lemma BetterInvertCarExecutesAtomicMovesDuringSingeton : 
    forall (m:AtomicMove) (tstart tend : Time)  (p:tstart ≤ tend),
    CarExecutesAtomicMovesDuring [m] tstart tend p
    ->  {pr : tstart < tend | CarExecutesAtomicMoveDuring m pr}.
  Proof.
    intros? ? ? ? Ha.
    inverts Ha.
  *)
    Lemma CarExecutesAtomicMovesDuring_wd :
    forall ml mr,
         ml = mr
 -> forall tstartl tstartr tendl tendr 
      (pl :tstartl ≤ tendl) (pr :tstartr ≤ tendr),
    tstartl = tstartr
    -> tendl = tendr
    -> CarExecutesAtomicMovesDuring ml _ _ pl
    -> CarExecutesAtomicMovesDuring mr _ _ pr.
  Proof using Type.
   intros ? ? meq.
   induction meq; intros ? ? ? ? ? ? ? ? Hl.
   - inverts Hl. constructor. rewrite <- H, pe. assumption.
   - inverts Hl as Hl1 Hl2.
    eapply IHmeq in Hl2; eauto; [| reflexivity].
     eapply CarExecutesAtomicMoveDuring_wd in Hl1; eauto; [| reflexivity].
    econstructor; eauto.
    Unshelve. Focus 2. rewrite <- H1. assumption.
    rewrite <- H0. assumption.
  Qed.
    
  Global Instance CarExecutesAtomicMovesDuring_ProperM (tstart tend : Time)  (p :tstart ≤ tend) :
    Proper (equiv ==> iff) (fun m => CarExecutesAtomicMovesDuring m tstart tend p).
  Proof using Type.
    intros ? ? ?. split; apply CarExecutesAtomicMovesDuring_wd; 
    eauto 1 with relations.
  Qed.

  

Section Wriggle.
(** * The Wriggle move
Now consider a 
#<href="https://rigtriv.wordpress.com/2007/10/01/parallel-parking/">wiggle motion</a>#
and characterize the the change in car's position and orientation caused
by this motion. 
The word "wriggle" was perhaps coined by Nelson in his 1967 book Tensor analysis.
Informally it denotes the following motion : 

  -steer (i.e rotate the steering wheel with brakes firmly pushed), 
  -drive (while keeping the steering wheel fixed),
  -reverse steer,
  -reverse drive

  Wiggle is parametrized by a nonzero [turnCurvature] and a drive distance,
  both of which may be signed.
  *)
  Variable tc : IR.
  Hypothesis tcNZ : tc[#]0.
  Variable distance : IR.
  

(** In our formalism, wriggle is a composition of the following 2 atomic moves.
  *)
  
  Definition steerAndDrive : AtomicMove
    := {|am_tc := tc; am_distance := distance |}.
  Definition revSteerAndrevDrive : AtomicMove
    := {|am_tc := -tc; am_distance := -distance |}.

(** the distance covered during driving and reverse driving is exactly the same.
  TODO: let them be slightly different, e.g. upto epsilon
 *)
  Definition Wriggle : AtomicMoves 
    :=  [steerAndDrive; revSteerAndrevDrive].
  
  Variable tstart : Time.
  Variable tend : Time.
  Hypothesis timeInc : tstart ≤ tend.
  
  (** Now, we assume that the car executes the [Wriggle] move from time [tstart] to [tend],
    and characterize the position and orientation at [tend], in terms of their values at [tstart]. 
     In this document When we say "move" in natural language, we mean [AtomicMoves].
    *)
  Hypothesis amsc : CarExecutesAtomicMovesDuring Wriggle tstart tend 
                      (timeInc).
  
  
  Local Notation θs := ({theta acs} tstart).
  Local Notation Xs := ({X (position acs)} tstart).
  Local Notation Ys := ({Y (position acs)} tstart).

  
  Hint Unfold One_instance_IR : IRMC.
      
      
  
  Lemma Wriggleθ : {theta acs} tend =  θs + 2 * tc * distance.
  Proof using amsc.
    invertAtomicMoves. rename Hf into amscrl.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl. rewrite amscl in amscrl.
    rewrite amscrl.
    autounfold with IRMC. ring.    
  Qed.

  (** just to show that the car doesn't end up to the initial position after wriggle.
     This equation is not needed for anything else. *)
  Lemma WriggleX : {X (position acs)} tend =  Xs +
        ((2* Sin (θs + tc * distance) 
            - Sin (θs + 2 * tc * distance)  - Sin θs) [/] tc [//] tcNZ).
  Proof using All.
    pose proof Wriggleθ as XX.
    invertAtomicMoves.
    rename amscl into Hl.
    rename Hf into Hrr.
    pose proof Hl as Hlt.
    apply AtomicMoveθ in Hlt.
    apply AtomicMoveX with (tcNZ:= tcNZ) in Hl.
    apply AtomicMoveXT with (tcNZ:= tcnegNZ _ tcNZ) in Hrr.
    Local Opaque Cos Sin.
    simpl in Hl, Hrr, Hlt.
    unfold cf_div in Hrr.
    rewrite XX in Hrr.
    rewrite Hrr. rewrite Hl.
    autounfold with IRMC. unfold cf_div.
    rewrite reciprocalNeg with (xp:=tcNZ).
    rewrite cring_inv_mult_lft.
    rewrite <- cring_inv_mult_rht.
    setoid_rewrite minusInvR.
    rewrite Hlt.
    autounfold with IRMC. unfold cg_minus. simpl.
     ring.
  Qed.

End Wriggle.

(*  Lemma Wriggleθ2  
  `{CarExecutesAtomicMovesDuring (Wriggle tc distance) tstart tend p} :
  {theta acs} tend =  {theta acs} tstart + 2 * tc * distance.
  Proof.
    
    invertAtomicMoves. rename Hf into amscrl.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl. rewrite amscl in amscrl.
    rewrite amscrl.
    autounfold with IRMC. ring.    
  Qed.
*)


Section Invertability.
(** * Invertability of moves 

It turns out that any Wriggle move is reversible (invertible).
Wriggle-inverse is a part of the sideways-move we will study next.
The sideways move comprises of 6 atomic moves and makes the car move sideways in little space.

To define Wriggle-inverse, we study invertability of moves in general,
and prove:
 -1) Every atomic move is inverible : keep the steering wheel at
the same position as before and then drive the same amount in 
the opposite direction.
 -2) The inverse of a list of atomic moves is the reverse of
the list of iverses of those atomic moves.


First we define what it means for a move to be an inverse of another.
*)

  Definition MovesIdentity (ams : AtomicMoves) :=
    ∀ (tstart tend : Time)  (p: tstart ≤ tend),
      CarExecutesAtomicMovesDuring ams tstart tend p
      -> (posAtTime acs tstart = posAtTime acs tend 
          /\ {theta acs} tstart = {theta acs} tend).

  (** [MovesIsInverse ams amsr] implies [MovesIdentity (ams ++ amsr)],
    but the other direction many not be true 
     This extra strength is useful because
    in the sideways move below, Wriggle-inverse does not immediately
    follow the Wriggle-move. *)
    
    
(*         TODO : quantify over [acs]. *)
  Definition MovesInverse (ams amsr : AtomicMoves) :=
    ∀ 
      (tstart tend : Time)  (p: tstart ≤ tend)
      (tstartr tendr : Time)  (pr: tstartr ≤ tendr),
      CarExecutesAtomicMovesDuring ams tstart tend p
      -> CarExecutesAtomicMovesDuring amsr tstartr tendr pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> (posAtTime acs tend - posAtTime acs tstart
          = posAtTime acs tstartr - posAtTime acs tendr
          /\ {theta acs} tstart = {theta acs} tendr).



(** if each atomic move is executed monotonically, we can aslo
    relate the confinements of the car in axis aligned rectangles.*)
  Definition MonotonicMovesInverse (ams amsr : AtomicMoves)  :=
    MovesInverse ams amsr /\
    ∀ (cd : CarDimensions ℝ) (confineRect: Line2D IR)
      (tstart tend : Time)  (p: tstart ≤ tend)
      (tstartr tendr : Time)  (pr: tstartr ≤ tendr),
      CarMonotonicallyExecsAtomicMovesDuring ams tstart tend p
      -> CarMonotonicallyExecsAtomicMovesDuring amsr tstartr tendr pr
      -> confinedDuring tstart tend cd confineRect
      -> confinedDuring tstart tend cd 
          (confineRect + '(posAtTime acs tendr - posAtTime acs tstart)).


  Definition CarExecutesAtomicMovesDuringAux  
      (tstart tend : Time)  (p: tstart ≤ tend) m
       := CarExecutesAtomicMovesDuring m tstart tend p .
  
   Lemma foldForProperAM : ∀ m 
      (tstart tend : Time)  (p: tstart ≤ tend),
      CarExecutesAtomicMovesDuring m tstart tend p ≡
      CarExecutesAtomicMovesDuringAux tstart tend p m.
   Proof using Type. reflexivity. Qed.

  Global Instance CarExecutesAtomicMovesDuringAux_Proper (tstart tend : Time)  (p :tstart ≤ tend) :
    Proper (equiv ==> iff) (CarExecutesAtomicMovesDuringAux tstart tend p).
  Proof using Type.
    apply CarExecutesAtomicMovesDuring_ProperM.
  Qed.

  Global Instance MovesInverseProper : Proper 
    (equiv ==> equiv ==> iff)  MovesInverse.
  Proof using Type.
    intros ? ? ? ? ? ?. unfold MovesInverse.
    setoid_rewrite (foldForProperAM x).
    setoid_rewrite (foldForProperAM x0).
    setoid_rewrite  H.
    setoid_rewrite  H0.
    tauto.
  Qed.
      

        
  Definition AtomicMoveInv (m : AtomicMove) : AtomicMove
      := {|am_tc := am_tc m; am_distance := -(am_distance m) |}.

  Definition AtomicMovesInv (ms : AtomicMoves) : AtomicMoves
      := rev (List.map AtomicMoveInv ms).

  Lemma atomicMoveInvertibleθ :
    ∀ m
      (tstart tend : Time)  (p: tstart < tend)
      (tstartr tendr : Time)  (pr: tstartr < tendr),
      CarExecutesAtomicMoveDuring m  p
      -> CarExecutesAtomicMoveDuring (AtomicMoveInv m)  pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> ({theta acs} tstart = {theta acs} tendr).
  Proof using Type.
    intros m ? ? ? ? ? ? amscl amscrl Ht.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl.
    rewrite amscrl, Ht, amscl.
    IRring.
  Qed.

  (** The equations for X coordinate are different, based on whether the steering wheel is perfectly
      straight or not. The double negation trick works while proving equality *)
  Lemma atomicMoveInvertibleXY :
    ∀ m
      (tstart tend : Time)  (p: tstart < tend)
      (tstartr tendr : Time)  (pr: tstartr < tendr),
      CarExecutesAtomicMoveDuring m  p
      -> CarExecutesAtomicMoveDuring (AtomicMoveInv m)  pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> (posAtTime acs tend - posAtTime acs tstart 
              = posAtTime acs tstartr - posAtTime acs tendr).
  Proof using Type.
    intros m ? ? ? ? ? ? amscl amscrl Hte.
    pose proof amscl as Htt.
    eapply atomicMoveInvertibleθ in Htt; eauto.
    eapply stable. 
      Unshelve. Focus 2. apply StableEqCart2D.
           apply StableEqIR;fail.
    pose proof (decideEdDN (am_tc m) [0]) as Hd.
    eapply DN_fmap;[exact Hd|]. clear Hd. intro Hd.
    destruct Hd as [Hd | Hd].
    - apply AtomicMoveZFinal with (pr := p) in amscl;
        [| exact Hd].
      apply AtomicMoveZFinal with (pr := pr) in amscrl;
        [| exact Hd]. repnd.
      simpl in amsclr, amscrlr.
      rewrite amscrlr,  amsclr, Hte, amscll.
      unfold cast, castCRCart2DCR. rewrite sameXYNegate.
      ring.
    - apply AtomicMoveXYT with (tcNZ:= Hd) in amscl.
      eapply AtomicMoveXYT  in amscrl.
      Unshelve. Focus 2. apply Hd;fail.
      simpl in amscl, amscrl.
      rewrite amscrl, Hte, amscl, Htt.
       split; simpl; IRring.
    Qed.

  Lemma atomicMoveInvertible :
    ∀ (m : AtomicMove), MovesInverse [m] [AtomicMoveInv m].
  Proof using Type.
    intros m ? ? ? ? ? ? ?.
    invertAtomicMoves.
    intros ? ?.    
    invertAtomicMoves.
    split.
    - eapply atomicMoveInvertibleXY; eauto.
    - eapply atomicMoveInvertibleθ in Hf0; eauto.
  Qed.

  Lemma atomicMonoMoveInvertible :
    ∀ (m : AtomicMove), MonotonicMovesInverse [m] [AtomicMoveInv m].
  Proof.
    intros m. split;[apply atomicMoveInvertible|].
    intros ? ? ? ? ? ? ? ? Hcm Hcm3 Hcon.
    invertAtomicMoves.
    intros t tp.
  Abort.

  Lemma MoveInvInvolutive : ∀ (m : AtomicMove), 
    AtomicMoveInv (AtomicMoveInv m) = m.
  Proof using .
    intros m.
    destruct m. unfold AtomicMoveInv, equiv, Equiv_AtomicMove. simpl.
    split; [| reflexivity]. apply negate_involutive.
  Qed.

  Lemma movesControlsApp : ∀ (l r : AtomicMoves) (tstart tend: Time)
    (pr : tstart ≤ tend),
    CarExecutesAtomicMovesDuring (l++r) _ _ pr
    -> exists (tmid : Time), exists (p : tstart ≤ tmid ≤ tend),
         CarExecutesAtomicMovesDuring l tstart tmid (proj1 p)
        /\ CarExecutesAtomicMovesDuring r tmid tend (proj2 p).
  Proof using Type.
    induction l; intros.
    - exists tstart. eexists. split; auto;[constructor; reflexivity| ].
      simpl in H.
      Unshelve. Focus 2. split;[apply leEq_reflexive | exact pr].
      eapply CarExecutesAtomicMovesDuring_wd; eauto; reflexivity.
    - simpl in H.
      invertAtomicMoves.
      eapply IHl in Hr; eauto.
      destruct Hr as [tmmid  Hr]. 
      destruct Hr as [pm Hr].
      repnd.
      exists tmmid. eexists.
      split; eauto.
      Focus 2.
        eapply CarExecutesAtomicMovesDuring_wd; eauto; reflexivity.
      econstructor; eauto.
      Unshelve.
      split; eauto 2 with CoRN.
      autounfold with IRMC. unfold Le_instance_Time.
       clear Hl.
      apply timeLtWeaken in pl.
      eauto 3 with CoRN.
  Qed.
  
  Lemma atomicMoveInvertibleRev :
    ∀ (m : AtomicMove), MovesInverse  [AtomicMoveInv m] [m].
  Proof using Type.
    intros m. remember [AtomicMoveInv m].
    setoid_rewrite <- MoveInvInvolutive.
    subst.
    apply atomicMoveInvertible.
  Qed.
    
    
  
  Lemma MovesControlsSingle : ∀ (m : AtomicMove) (tstart tend: Time)
    (pr : tstart < tend),
    @CarExecutesAtomicMoveDuring m tstart tend pr
    -> CarExecutesAtomicMovesDuring [m] tstart tend (timeLtWeaken pr).
  Proof using Type.
    intros. econstructor; eauto. econstructor. reflexivity.
    Unshelve. apply leEq_reflexive.
  Qed.

   
   

  Lemma atomicMovesInvertibleAux :
    ∀ (m : AtomicMoves), MovesInverse (AtomicMovesInv m) m.
  Proof using Type.
    induction m as [| h tl Hind]; intros ? ? ? ? ? ? Hm Hrm Ht;
      unfold AtomicMovesInv in Hrm; simpl in Hrm.
    - invertAtomicMoves. unfold posAtTime. rewrite <- Hml in Ht. 
      rewrite Hrml in Ht.
      rewrite Ht, Hml, Hrml. split;[split; simpl | reflexivity];
      repeat rewrite plus_negate_r; reflexivity.
    - invertAtomicMoves. rename tmid into tmidr.
      unfold AtomicMovesInv in Hm.
      rename Hm into Hl.
      simpl in Hl.
      apply movesControlsApp in Hl.
      destruct Hl as [tmid Hl].
      destruct Hl as [prr Hl].
      repnd.
      apply MovesControlsSingle in Hrml.
      eapply atomicMoveInvertibleRev in Hrml; eauto.
      specialize (Hrml Ht). repnd.
      eapply Hind in Hrmr; eauto.
      symmetry in Hrmlr.
      specialize (Hrmr Hrmlr). repnd. clear Hrmlr.
      split; [clear Hrmrr | exact Hrmrr].
      pose proof (@sg_op_proper _ _ plus  _ _ _ Hrmll _ _ Hrmrl) as Hadd.
      clear Hrmll  Hrmrl.
      unfold sg_op in Hadd.
      ring_simplify in Hadd.
      exact Hadd.
  Qed.
  
  Lemma MovesInvInvolutive : ∀ (m : AtomicMoves), 
    AtomicMovesInv (AtomicMovesInv m) = m.
  Proof using .
    induction m;[reflexivity |].
    unfold AtomicMovesInv. simpl.
    rewrite map_app.
    rewrite map_cons.
    rewrite rev_app_distr.
    simpl.
    rewrite MoveInvInvolutive.
    constructor; auto.
  Qed.


  Lemma atomicMovesInvertible :
  ∀ (m : AtomicMoves), MovesInverse m (AtomicMovesInv m).
  Proof using Type.
    intros m. remember (AtomicMovesInv m).
    setoid_rewrite <- (MovesInvInvolutive m).
    subst.
    apply atomicMovesInvertibleAux.
  Qed.
  
End Invertability.


Section Sideways.

(** * The sideways move

Adding just one atomic move to the [SidewaysAux] move defined below
will get us to the sideways move. After [SidewaysAux],
as we will prove,
the car's orientation is same as that in the original state, but
it's position has shifted a bit, both along the car's orientaition and orthogonal to it.
[SidewaysAux] is just a straight-drive move inserted between
a wriggle and its inverse.
Note that without this insertion, we would have been back
to where we started.
*)
  Variable tc : IR.
  Hypothesis tcNZ : tc[#]0.
  Variable wdistance : IR.
  Variable ddistance : IR.
  
  Local Notation SWriggle := (Wriggle tc wdistance).
  Local Notation SWriggleInv := (AtomicMovesInv SWriggle).
  
  (** Drive a distance of [ddistance]
    with front wheels perfectly straight.*)  
  Local Notation DriveStraight := {| am_distance := ddistance ; am_tc := 0|}.

  Definition SidewaysAux : AtomicMoves 
    := SWriggle ++ [DriveStraight] ++ SWriggleInv.

  
  (** The car's orientation at the end is same as that at the start.
     [θAtW] denotes the car's orientation at the completion of the [SWriggle] move. 
     For any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
     *)
  Lemma SidewaysAuxState : forall  (tstart tend : Time) (timeInc : tstart ≤ tend),
  (CarExecutesAtomicMovesDuring SidewaysAux tstart tend timeInc)
  ->
  let θs := ({theta acs} tstart) in 
  let θAtW := θs + 2 * tc * wdistance  in
  {theta acs} tend =  θs /\
    posAtTime acs tend = (posAtTime acs tstart)
      + ('ddistance) * (unitVec θAtW).
  Proof using Type.
    intros ? ? ? amsc.    
    unfold SidewaysAux in amsc.
    apply movesControlsApp in amsc.
    destruct amsc as [tds Hams]. (* ds for drive straight *)
    destruct Hams as [pds Hams].
    repnd. rename Hamsl into Hw. (* w for wiggle *)
    apply movesControlsApp in Hamsr.
    destruct Hamsr as [twr Hamsr]. (* ds for drive straight *)
    destruct Hamsr as [pwr Hams]. repnd.
    rename Hamsl into Hds.
    rename Hamsr into Hwr.
    pose proof Hw as Hwb. (* needed for θAtW *)
    eapply atomicMovesInvertible in Hw; eauto.
    specialize (Hw Hwr). clear Hwr.
    apply Wriggleθ in Hwb.
    invertAtomicMoves.
    apply AtomicMoveZFinal in Hf;[|unfold amNoTurn;  reflexivity].
    simpl in Hf. repnd.
    specialize (Hw Hfl).
    repnd. symmetry in Hwr.
    split;[assumption|]. rewrite Hwb in Hfr.
    clear Hwb Hwr Hfl pll. rewrite Hfr in Hwl. clear Hfr.
    rewrite  <- (@plus_assoc (Cart2D IR)) in Hwl; [|eauto with typeclass_instances].
    apply (@left_cancellation ) in Hwl; [|apply groups.LeftCancellation_instance_0].
    apply (RingNegateProper ) in Hwl.
    rewrite negate_involutive in Hwl.
    rewrite Hwl. ring.
  Qed.

  (** After [SidewaysAux], the car is in the same orientation as before, but it has position
    has changed. For a sideways move, we just have drive straight to cancel
    the component of that position change along the car's orientation.
    We get this component by taking the dot product of the position change with the unit vector
    along the car's orientation.
    Formally, a sideways move is one where the car's position shifts in a direction
    orthogonal to its orientation.
    *)
  Local Notation DriveStraightRev 
    := {| am_distance := - ddistance * Cos (2 * tc * wdistance) ; am_tc := 0|}.

  Definition SidewaysMove : AtomicMoves 
    := SidewaysAux ++ [DriveStraightRev].
    
  (** The car's final orientation is same as before, and 
  its position changes in the direction that is at a right angle [(½ * π)]
  to its orientation, i.e., it is a sideways move. 
  The distance moved is [ddistance * Sin  θw].

  As mentioned before, for any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
  *)
  
  Lemma SidewaysState : forall  (tstart tend : Time) (timeInc : tstart ≤ tend),
  (CarExecutesAtomicMovesDuring SidewaysMove tstart tend timeInc)
  ->
  let θs := ({theta acs} tstart) in 
  let θw := 2 * tc * wdistance  in
    {theta acs} tend =  θs /\
    posAtTime acs tend = (posAtTime acs tstart) 
      + ('(ddistance * Sin  θw)) * unitVec (θs + (½ * π)).
  Proof using Type.
    intros ? ? ? amsc.
    unfold SidewaysMove in amsc. simpl.
    apply movesControlsApp in amsc.
    destruct amsc as [tds Hams]. (* ds for drive straight *)
    destruct Hams as [pds Hams]. repnd.
    apply SidewaysAuxState in Hamsl.
    invertAtomicMoves.
    apply AtomicMoveZFinal in Hf;[|unfold amNoTurn;  reflexivity].
    simpl in Hf. repnd.
    rewrite Hamsll in Hfl.
    rewrite Hamsll in Hfr.
    split;[assumption|]. clear Hamsll Hfl.
    rewrite Hamslr in Hfr. clear Hamslr pll pdsl pdsr.
    remember (2 * tc * wdistance) as θw.
    clear Heqθw. unfold cast, castCRCart2DCR in Hfr.
    rewrite <- sameXYMult in Hfr.
    rewrite sameXYNegate in Hfr.
    rewrite  <- (@mult_assoc (Cart2D IR)) in Hfr ; [|eauto with typeclass_instances].
    
    rewrite <- negate_mult_distr_l in Hfr.
    rewrite negate_mult_distr_r in Hfr.
    rewrite  <- (@plus_assoc (Cart2D IR)) in Hfr; [|eauto with typeclass_instances].
    setoid_rewrite  <- (@plus_mult_distr_l (Cart2D IR)) in Hfr;
       [|eauto with typeclass_instances].
    rewrite unitVecLemma1 in Hfr. unfold cast, castCRCart2DCR.
    rewrite <- sameXYMult.
    rewrite  <- (@mult_assoc (Cart2D IR)); [|eauto with typeclass_instances].
    rewrite PiBy2DesugarIR.
    exact Hfr.
  Qed.

End Sideways.

End Props.
