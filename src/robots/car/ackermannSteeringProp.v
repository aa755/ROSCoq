
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
Require Import errorBounds.

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

Global Instance CastCarDim `{Cast A B} 
  : Cast (CarDimensions A) (CarDimensions B) :=
fun a =>  Build_CarDimensions 
            ('lengthFront a)
            ('lengthBack a) 
            ('width a).

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
Definition plausibleCarDim (cd : CarDimensions IR) : Prop :=
  0 ≤ lengthFront cd /\  0 ≤ width cd /\ 0 ≤ lengthBack cd.

Definition nonTrivialCarDim (cd : CarDimensions Q) :=
  0 < lengthFront cd  ∧  0 < width cd ∧ 0 < lengthBack cd.


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

  Lemma absSmall0 : forall x:IR,
    AbsSmall 0 x <-> x=0.
  Proof using.
    intros ?. split; intros Xx.
  - apply AbsSmall_imp_AbsIR in Xx.
    apply AbsIRLe0. assumption.
  - rewrite Xx. split; try reflexivity;[].
    setoid_rewrite negate_0. reflexivity.
  Qed.

(* TODO: It suffices to assume it for just rational times, because of continuity *)  
  Hypothesis fixed : forall (t :Time), 
    (tstart ≤ t ≤ tend)  -> {turnCurvature acs} t = tc.

  Lemma fixed2 : ∀ (t:Time), (tstart ≤ t ≤ tend)
    -> AbsSmall 0 (({turnCurvature acs} t) - tc).
  Proof using fixed.
    intros. apply absSmall0.
    apply equal_by_zero_sum.
    apply fixed. assumption.
  Qed.

  Lemma fixed3 : ∀ (t1:Time), (tstart ≤ t1 ≤ tend)
    -> forall t, (tstart ≤ t ≤ t1)
    -> AbsSmall 0 (({turnCurvature acs} t) - tc).
  Proof using fixed.
    intros. apply fixed2.
    split; try tauto.
    repnd.
    eapply transitivity; eauto.
  Qed.

  (** [theta] at time [t] is also needed obtain position at time [t] by integration *)
  Lemma fixedSteeringTheta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
(** ib denotes the pair of numbers that goes at the bottom and at the top of ∫ *)
    let ib := @mkIntBnd _ tstart t (proj1 p) in
    ({theta acs} t - {theta acs} tstart) = tc* (∫ ib (linVel acs)).
  Proof using fixed.
    intros ? Hb ?.
    pose proof (fixed3 _ Hb) as Ht.
    apply errorBounds.thetaBall with (timeInc:=proj1 Hb) in Ht.
    rewrite mult_0_l in Ht.
    setoid_rewrite AbsIR_eq_x in Ht;[| reflexivity].
    apply absSmall0 in Ht.
    apply equal_by_zero_sum. assumption.
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
    pose proof (fixed3 _ Hb) as Ht.
    apply errorBounds.fixedSteeeringX
        with (timeInc:=proj1 Hb) (tcNZ0:=tcNZ) in Ht.
    unfold cf_div in Ht.
    rewrite mult_0_l in Ht.
    setoid_rewrite mult_0_l in Ht.
    setoid_rewrite AbsIR_eq_x in Ht;[| reflexivity].
    apply absSmall0 in Ht.
    apply equal_by_zero_sum. assumption.
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
    pose proof (fixed3 _ Hb) as Ht.
    apply errorBounds.fixedSteeeringY
      with (timeInc:=proj1 Hb) (tcNZ0:=tcNZ) in Ht.
    unfold cf_div in Ht.
    rewrite mult_0_l in Ht.
    setoid_rewrite mult_0_l in Ht.
    setoid_rewrite AbsIR_eq_x in Ht;[| reflexivity].
    apply absSmall0 in Ht.
    apply equal_by_zero_sum. assumption.
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

  Lemma holdsDuringAMIf : forall(P: (Rigid2DState IR) -> Prop)
    `{@Setoid_Morphism  _ _ _ _ P},
    noSignChangeDuring (linVel acs) tstart tend
    ->
    (∀ (θ : IR), inBetweenR θ ({theta acs} tstart) ({theta acs} tend)
      -> P (turnRigidStateAtθ (rigidStateAtTime acs tstart) turnRadius θ))
     ->  (∀ t : Time, tstart ≤ t ≤ tend → P (rigidStateAtTime acs t)).
  Proof using fixed tstartEnd.
    intros ? ?  Hn hh t Hb.
    specialize (hh ({theta acs}t)).
    rewrite turnRigidStateAtθCorrect;[| assumption].
    apply hh.
    apply thetaMonotone; try assumption.
    pose proof (fst (less_conf_ap _ _ _) tcNZ) as Hdec.
    autounfold with IRMC.
    destruct Hdec; [left|right]; eauto 2 with CoRN.
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
    
    intros ? ? Hn hh t Hb. apply holdsDuringAMIf; auto.
    constructor; eauto 2 with typeclass_instances.
    unfold Setoid. eauto 2 with typeclass_instances.
    intros ? ? Heq. rewrite Heq. reflexivity.
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

