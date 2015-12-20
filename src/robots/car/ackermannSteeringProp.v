
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
Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Export ackermannSteering.
Require Import MCMisc.tactics.
Require Import fastReals.interface.
Require Import fastReals.misc.

  Require Import IRMisc.LegacyIRRing.
  Add Ring cart2dir : Cart2DIRRing.

Require Export CartIR.
Require Import geometry2D.
Require Import geometry2DProps.

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).
  Local Notation  "∫" := Cintegral.


(** 
* Characterizing the motion under Ackermann steering.

This file is highly experimental.
*)



Hint Unfold cos CosClassIR sin SinClassIR min MinClassIR  max MaxClassIR: IRMC.
Hint Unfold cos CosClassIR sin SinClassIR min MinClassIR  max MaxClassIR: AbstractR.


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


Global Instance properPosAtTime {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature) :
Proper (equiv ==> equiv) (posAtTime acs).
Proof.
  intros ? ? Heq; split; simpl;
  rewrite Heq; reflexivity.
Qed.


Global Instance properRigid2DState {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature) :
Proper (equiv ==> equiv) (rigidStateAtTime acs).
Proof.
  intros ? ? Heq; split; simpl;
  rewrite Heq; reflexivity.
Qed.

Global Instance EquivCarDim `{Equiv A}: Equiv (CarDimensions A) := fun a b => (width a = width b) 
  /\ (lengthFront a = lengthFront b)
  /\ (lengthBack a = lengthBack b).

Global Instance ProperCarDimLengthFront `{Equiv A}: 
Proper (equiv ==> equiv) (@lengthFront A).
Proof.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

Global Instance ProperCarDimLengthBack `{Equiv A}: 
Proper (equiv ==> equiv) (@lengthBack A).
Proof.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

Global Instance ProperCarDimWidth `{Equiv A}: 
Proper (equiv ==> equiv) (@width A).
Proof.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

(**width needs to be nonzero so that we can take its reciprocal in an arctan.
  others can also be required to be strictly positive*)

Definition nonTrivialCarDim (cd : CarDimensions IR) :=
  0 ≤ lengthFront cd  and  0 [<] width cd and 0 ≤ lengthBack cd.

Global Instance EquivalenceCarDim  `{e:Equiv A}
  `{Equivalence _ e}
   : Equivalence EquivCarDim.
Proof using .
  unfold equiv, EquivCarDim. split.
  - intros x. destruct x. simpl. split; auto with *.
  - intros x y. destruct x,y. simpl. intros Hd; repnd;
      split; auto with relations.

  - intros x y z. destruct x,y,z. simpl. intros H0 H1.
    repnd.
    split; eauto 3
    with relations.
Qed.

Global Instance ProperCarMinMax : Proper
    (equiv ==> equiv ==> equiv) (@carMinMaxXY IR _ _ _ _ _ _ _ _ _ _).
Proof using.
  intros ? ? H0 x y Heq. unfold carMinMaxXY. simpl.
  unfold backLeft, frontLeft, frontRight, backRight.
  rewrite H0.
  rewrite Heq. reflexivity.
Qed.


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
Context {maxTurnCurvature : Qpos}
(acs : AckermannCar maxTurnCurvature).

  Variable tstart : Time.
  Variable tend : Time.

  Hypothesis tstartEnd : (tstart ≤ tend).

  Definition confinedDuring (cd :CarDimensions IR) (rect: Line2D IR) :=
   forall  (t :Time),
    tstart ≤ t ≤ tend
    → carMinMaxXY cd (rigidStateAtTime acs t) ⊆ rect.

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

  Section CornersCircle.
  Variable cd :CarDimensions IR.

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

  End CornersCircle.
    Require Import MCMisc.rings.

  Definition turnRigidStateAtθ (init : Rigid2DState IR) 
  (tr θ : IR)
  := 
  let θi := θ2D init in
  {|pos2D := pos2D init + {|X:=Sin θ - Sin θi; Y:=Cos θi - Cos θ|}*'tr;
    θ2D := θ|}.
  
  Global Instance ProperturnRigidStateAtθ: Proper 
  (equiv ==> equiv ==> equiv ==> equiv) turnRigidStateAtθ.
  Proof using.
    intros ? ? H1 ? ? H2 ? ? H3.
    unfold turnRigidStateAtθ.
    rewrite H1.
    rewrite H2.
    rewrite H3. reflexivity.
  Qed.
  
  Lemma turnRigidStateAtθCorrect: forall (t :Time)  (p: tstart ≤ t ≤ tend),
    rigidStateAtTime acs t 
    = turnRigidStateAtθ 
            (rigidStateAtTime acs tstart) 
            turnRadius
            ({theta acs} t).
  Proof using fixed.
    intros ? ?.
    split;[| reflexivity].
    simpl. apply RingShiftMinus.
    split;simpl;[apply fixedSteeeringX | apply fixedSteeeringY];
    assumption.
  Qed.
    
  Lemma auxConfinedDuringAMIf : forall (confineRect : Line2D IR) cd,
    noSignChangeDuring (linVel acs) tstart tend
    ->
    (∀ (θ : IR), inBetweenR θ ({theta acs} tstart) ({theta acs} tend)
  -> carMinMaxXY cd
     (turnRigidStateAtθ (rigidStateAtTime acs tstart) turnRadius θ) 
           ⊆ confineRect)
     ->  confinedDuring cd confineRect.
  Proof using fixed tstartEnd.
    intros ? ? Hn hh t Hb.
    specialize (hh ({theta acs}t)).
    rewrite turnRigidStateAtθCorrect;[| assumption].
    apply hh.
    apply thetaMonotone; try assumption.
    pose proof (fst (less_conf_ap _ _ _) tcNZ) as Hdec.
    autounfold with IRMC.
    destruct Hdec; [left|right]; eauto 2 with CoRN.
  Qed.
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
End Cases.
