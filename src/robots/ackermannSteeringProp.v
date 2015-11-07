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

  Add Ring RisaRing: (CRing_Ring IR).

Require Export CartIR.


(** 
* Characterizing the motion under Ackermann steering.

This file is highly experimental.
*)
Definition posAtTime {maxTurnCurvature : Qpos} (ic : AckermannCar maxTurnCurvature) (t: Time) : Cart2D IR :=
  {| X:= {X (position ic)} t ; Y := {Y (position ic)} t |}.
  
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

TODO: Ideally, we should let the turn curvature of them vary a bit 
(upto some epsilon) during the process.
This will SIGNIFICANTLY complicate the integrals.
*)


Section Cases.

  Variable tstart : Time.
  Variable tend : Time.

  Hypothesis tstartEnd : (tstart ≤ tend).

  Local Notation θ0 := ({theta acs} tstart).
  
  (** we will consider 2 classes of motions between [tstart] and [tend]. These classes suffice for our purpose
    1) move with fixed steering wheel ([turnCurvature])
    2) rotate the steering wheel while remaining stationary.
  *)

  Section FixedSteeringWheel.
  Variable tc : IR.

(* TODO: It suffices to assume it for just rational times, because of continuity *)  
  Hypothesis fixed : forall (t :Time), 
    (tstart ≤ t ≤ tend)  -> {turnCurvature acs} t = tc.

  (** [theta] at time [t] is also needed obtain position at time [t] by integration *)
  Lemma fixedSteeringTheta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
(* ib denotes the pair of numbers that goes at the bottom and at the top of ∫ *)
    let ib := @mkIntBnd _ tstart t (proj1 p) in
    ({theta acs} t - {theta acs} tstart) = tc* (∫ ib (linVel acs)).
  Proof.
    intros ? Hb ?.
    setoid_rewrite <- TBarrowScale;
      [| apply (derivRot acs)|];[reflexivity|].
    intros tb Hbb.  rewrite mult_comm.
    simpl. apply mult_wd;[| reflexivity].
    apply fixed. unfold intgBndL, intgBndR in Hbb.  simpl in Hbb.
    repnd. autounfold with IRMC. unfold Le_instance_Time.
    split; eauto 2 with CoRN.
  Qed.


  (** we consider 2 subcases. First the case when the front wheels are not straight, i.e. the 
      turn curvature is nonzero. Due to "divide by 0" issues, integration has to be done differently
      in these cases*)

  Section TCNZ.
  (**Needed because [tc] shows up as a denominator
     during integration below in [fixedCurvX]. The 0 case perhaps 
    needs to be handled separately, and constructively!*)
  Hypothesis tcNZ : (tc [#] 0).


  (** [X] coordinate of the [position] at a given time. Note that in CoRN,
      division is a ternary operator. [a[/]b[//][bp]] denotes the real number [a]
      divided by the non-zero real number [b], where [bp] is the proof of non-zero-hood
      of [b].
   *)
  Lemma fixedSteeeringX : forall (t :Time) (_: tstart ≤ t ≤ tend),
    ({X (position acs)} t - {X (position acs)} tstart) =  
        ((Sin ({theta acs} t) - Sin ({theta acs} tstart)) [/] tc [//] tcNZ).
  Proof.
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
      autorewrite with IContRApDown.
      rewrite fixed with (t:=tb); [ring |].
      autounfold with IRMC.  unfold Le_instance_Time.
      unfold inBounds in Hbb. simpl in Hbb. repnd.
      split; eauto 2 with CoRN.
  Qed.

  Lemma tcnegNZ : - tc [#] 0.
  Proof. 
    apply inv_resp_ap_zero. exact tcNZ.
  Qed.

  Lemma fixedSteeeringY : forall (t :Time) (_: tstart ≤ t ≤ tend),
    ({Y (position acs)} t - {Y (position acs)} tstart) =  
        ((Cos ({theta acs} tstart) - Cos ({theta acs} t)) [/] tc [//] tcNZ).
  Proof.
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
      autorewrite with IContRApDown.
      rewrite composeIContAp.
Local Opaque CFSine.
Local Opaque Sine.
      simpl. symmetry.
      pose proof (@pfwdef2 _ Sine ({theta acs} tb) (fst Continuous_Sin ({theta acs} tb) I) I) as Hr. 
      rewrite Hr.
      rewrite fixed with (t:=tb); [ring |].
      autounfold with IRMC.  unfold Le_instance_Time.
      unfold inBounds in Hbb. simpl in Hbb. repnd.
      split; eauto 2 with CoRN.
  Qed.

  End TCNZ.

  Section TC0.
  (** now consider the case when the front wheels are exactly straight *)
  Hypothesis tcNZ : (tc = 0).

  Lemma fixedStraightSteeringTheta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
      {theta acs} t = {theta acs} tstart.
  Proof.
  Abort.


  Lemma fixedStraightSteeeringX : forall (t :Time) (p: tstart ≤ t ≤ tend),
    let ib := @mkIntBnd _ tstart t (proj1 p) in
    ({X (position acs)} t - {X (position acs)} tstart) =  (∫ ib (linVel acs)) * Cos ({theta acs} tstart).
  Proof.
  Abort.

  Lemma fixedStraightSteeeringY : forall (t :Time) (p: tstart ≤ t ≤ tend),
    let ib := @mkIntBnd _ tstart t (proj1 p) in
    ({Y (position acs)} t - {Y (position acs)} tstart) =  (∫ ib (linVel acs)) * Cos ({theta acs} tstart).
  Proof.
  Abort.

  
  End TC0.
  
  End FixedSteeringWheel.
  Hint Unfold Le_instance_Time : IRMC.
  Section LinVel0.
  (** Now consider the second case where the steering wheel may move, but the car remains stationary *)
    Hypothesis lv0 :  forall (t :Time), 
      (tstart ≤ t ≤ tend)  -> {linVel acs} t = 0.

    Lemma LV0Theta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
        {theta acs} t = {theta acs} tstart.
    Proof.
      intros. eapply TDerivativeEq0;[tauto | apply derivRot|].
      intros tt Hb. simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.

 Local Opaque FCos.
    Lemma LV0X : forall (t :Time) (p: tstart ≤ t ≤ tend),
      {X (position acs)} t = {X (position acs)} tstart .
    Proof.
      intros. eapply TDerivativeEq0;[tauto | apply derivX|].
      intros tt Hb.
      simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.

    Lemma LV0Y : forall (t :Time) (p: tstart ≤ t ≤ tend),
      {Y (position acs)} t = {Y (position acs)} tstart .
    Proof.
      intros. eapply TDerivativeEq0;[tauto | apply derivY|].
      intros tt Hb.
      simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.


  End LinVel0.
  
(* TODO : given the car's dimensions, confine the whole car within 
  a "small, yet simple" region
  during the above motion. *)

End Cases.

Section AtomicMove.
(** We will build complex manueuvers out of the following bacic move :
turn the steering wheel so that the turnCurvature has a particular value ([tc]),
and then drive for a particular distance ([distance]).
Note that both [tc] and [distance] are signed -- the turn center can be on the either side,
and one can drive both forward and backward *)
  Record AtomicMove := mkAtomicMove
  {
     am_tc : IR;
     am_tcNZ : am_tc[#]0;
     am_distance : IR
  }.


  Variable tstart : Time.
  Variable tend : Time.
  Variable am : AtomicMove.
  
  
  Inductive Truncate (T:Type) : Prop :=
  | truncate : T -> Truncate T.
  
  (** The typeclass [Lt] is defined in the Prop universe. It cannot have constructive content.*)
  Global Instance Lt_instance_Time : Lt Time := fun x y => Truncate (x [<] y).

  Lemma timeLtWeaken : forall {a b: Time}, a < b  -> a ≤ b.
  Proof.
    intros ? ? H.
    destruct H as [X].
    (* autounfold with IRMC. unfold Le_instance_Time.
       info_eauto 2 with CoRN. *)
    apply less_leEq. exact X.
    Qed.

  
  (** what it means for the car's controls to follow the atomic move [am] during time [tstart] to [tend] *)
  Record AtomicMoveControls :=
  {
    am_tdrive : Time;
    am_timeInc : (tstart < am_tdrive < tend);
 
    am_steeringControls : ({turnCurvature acs} am_tdrive) = (am_tc am) 
      /\ forall (t:Time), (tstart ≤ t ≤ am_tdrive) 
          -> {linVel acs} t = 0;

 
  (** From time [tdrive] to [tend], the steering wheel is held fixed*)
    am_driveControls : forall (t:Time), (am_tdrive ≤ t ≤ tend) 
          ->  {turnCurvature acs} t = {turnCurvature acs} am_tdrive;
          
   am_driveDistance : 
      let pf := (timeLtWeaken (proj2 (am_timeInc))) in 
      let driveIb := (@mkIntBnd _ am_tdrive tend pf) in 
          (am_distance am) = ∫ driveIb (linVel acs)
  }.
  
  Hypothesis amc : AtomicMoveControls.
  
  Local Notation tc := (am_tc am).
  Local Notation tcNZ := (am_tcNZ am).
  Local Notation distance := (am_distance am).
  Local Notation tdrive := (am_tdrive amc).
  
  Lemma am_timeIncWeaken : (tstart ≤ tdrive ≤ tend).
    pose proof (am_timeInc amc).
    split; apply timeLtWeaken; tauto.
  Qed.


  Local Notation timeInc := am_timeIncWeaken.

  (** From time [tsteer] to [drive], the steerring wheel moves to attain a configuration 
    with turn curvature [tc]. The brakes are firmly placed pressed.*)

  (** Now, we characterize the position and orientation at [tdrive] and [tend] *)
  Local Definition θs := {theta acs} tstart.
  Local Definition Xs := {X (position acs)} tstart.
  Local Definition Ys := {Y (position acs)} tstart.



  Ltac timeReasoning :=
    autounfold with IRMC; unfold Le_instance_Time;
      destruct timeInc; eauto 2 with CoRN; fail.


  Lemma AtomicMoveθ : {theta acs} tend =  θs + tc * distance.
  Proof.
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
    unfold θs. rewrite <- driveControls.
    autounfold with IRMC. ring. 
  Qed.

  Lemma AtomicMoveX : {X (position acs)} tend =  Xs +
        ((Sin (θs + tc * distance) - Sin θs) [/] tc [//] tcNZ).
  Proof.
    pose proof (am_driveControls amc) as driveControlsb.
    pose proof (am_steeringControls amc) as steeringControls.
    setoid_rewrite (proj1 steeringControls) in driveControlsb.
    eapply  fixedSteeeringX with (t:= tend) (tcNZ:=tcNZ) in driveControlsb.
    Unshelve. Focus 2. timeReasoning.
    unfold cf_div in driveControlsb.
    rewrite AtomicMoveθ in driveControlsb.
    rewrite (fun p => LV0X tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
        | timeReasoning ].
    rewrite (fun p => LV0Theta tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
        | timeReasoning ].
    setoid_rewrite <- driveControlsb. simpl. unfold Xs. autounfold with IRMC. simpl. ring.
  Qed.

End AtomicMove.


Section CompositionOfAtomicMoves.


Section Wriggle.
(** Now consider a 
#<href="https://rigtriv.wordpress.com/2007/10/01/parallel-parking/">wiggle motion</a>#
and characterize the the change in car's position and orientation caused
by this motion. 
The word "wriggle" was perhaps coinde by Nelson in his 1967 book Tensor analysis,
and it denotes the following motion : 
  steer (i.e rotate the steering wheel with brakes firmly pushed), 
  drive (while keeping the steering wheel fixed),
  reverse steer
  reverse drive
*)


(** the start time of each of the above mentioned phases (r for reverse), 
    and the end time of the whole wiggle motion*)
  Variable tsteer : Time.
  Variable tdrive : Time.
  Variable trsteer : Time.
  Variable trdrive : Time.
  Variable tend : Time.

(** this is the time during which [turnCurvature] changes. any value will suffice *)
  Variable timeInc : (tsteer ≤ tdrive ≤ trsteer) /\   (trsteer ≤ trdrive ≤ tend).

(** constant curvature of the car after steering *)
  Variable tc : IR.
  Hypothesis tcNZ : tc[#]0.

(** Now we characterize the state of the controls during each of the 4 phases. First, the steering phase.
   At the end of this phase, the state of the steering wheel should be such that the [turnCurvature]
   is [tc]. Also, the position and orientation of the cars should not change, e.g. brakes firmly pressed.
   Note that our eventual goal is to not just show that the car's final state is correct (paralle parked),
   but also that it did not collide with other cars in the process, therefore, it is insufficient to
   characterize the position and orientation at just the endpoint of this phase.
 *)
  Hypothesis steeringControls : ({turnCurvature acs} tdrive) = tc 
      /\ forall (t:Time), (tsteer ≤ t ≤ tdrive) 
          -> (posAtTime acs t = posAtTime acs tsteer) /\ {theta acs} t = {theta acs} tsteer.
          
  Hypothesis driveControls : forall (t:Time), (tdrive ≤ t ≤ trsteer) 
          ->  {turnCurvature acs} t = {turnCurvature acs} tdrive.

  Definition driveIb := (@mkIntBnd _ tdrive trsteer (proj2 (proj1 timeInc))).
  Definition driveDistance := ∫ driveIb (linVel acs).

  Hypothesis rsteeringControls : ({turnCurvature acs} trdrive) = -tc 
      /\ forall (t:Time), (trsteer ≤ t ≤ trdrive) 
          -> (posAtTime acs t = posAtTime acs trsteer) /\ {theta acs} t = {theta acs} trsteer.

  Definition rdriveIb := (@mkIntBnd _ trdrive tend (proj2 (proj2 timeInc))).
  Definition rdriveDistance := ∫ rdriveIb (linVel acs).

  Hypothesis rdriveControls : forall (t:Time), (trdrive ≤ t ≤ tend) 
          ->  {turnCurvature acs} t = {turnCurvature acs} trdrive.

(** the distance covered during driving and reverse driving is exactly the same.
  TODO: let them be slightly different, e.g. upto epsilon
 *)
  Hypothesis driveDistanceSame : driveDistance = -rdriveDistance.

  (** Now, we characterize the position and orientation at endpoints of each phase*)
  Local Definition θs := {theta acs} tsteer.
  Local Definition Xs := {X (position acs)} tsteer.
  Local Definition Ys := {Y (position acs)} tsteer.



Ltac timeReasoning :=
  let Hl := fresh "Hl" in
  let Hr := fresh "Hr" in
    autounfold with IRMC; unfold Le_instance_Time;
      destruct timeInc as [Hl Hr]; destruct Hr; destruct Hl; eauto 2 with CoRN; fail.


  
      
  Lemma θAtEnd : {theta acs} tend =  θs + 2 * tc * driveDistance.
  Proof.
    eapply  fixedCurvTheta with (t:= tend) in rdriveControls.
    Unshelve. Focus 2. timeReasoning.
    simpl in rdriveControls.
    rewrite Cintegral_wd in rdriveControls;[| | reflexivity].
    Focus 2. instantiate (1 := rdriveIb). simpl. split; reflexivity; fail.
    rewrite (proj1 rsteeringControls) in rdriveControls.
    rewrite θAfterRSteer in rdriveControls.
    fold (rdriveDistance) in rdriveControls.
    rewrite cg_cancel_mixed with (y:= (θs + tc * driveDistance)).
    setoid_rewrite rdriveControls.
    setoid_rewrite  driveDistanceSame. autounfold with IRMC. unfold One_instance_IR.
    ring.
    Qed.
    
    
  Lemma XAfterDrive : {X (position acs)} trsteer =  Xs +
        ((Sin (θs + tc * driveDistance) - Sin θs) [/] tc [//] tcNZ).
  Proof.
    pose proof driveControls as driveControlsb.
    setoid_rewrite (proj1 steeringControls) in driveControlsb.
    eapply  posFixedCurvX with (t:= trsteer) (tcNZ:=tcNZ) in driveControlsb.
    Unshelve. Focus 2. timeReasoning.
    unfold cf_div in driveControlsb.
    rewrite θAfterDrive in driveControlsb.
    rewrite  (fun p => proj2 ((proj2 steeringControls) tdrive p)) in driveControlsb;
      [|timeReasoning].
    setoid_rewrite <- driveControlsb.
    autounfold with IRMC. unfold Xs.
    unfold posAtTime in steeringControls.
    unfold equiv, EquivCart in steeringControls.
    simpl in steeringControls.
    setoid_rewrite 
      (fun p =>  proj1 (proj1 ((proj2 steeringControls) tdrive p)));
      [simpl; ring |].
    timeReasoning.
  Qed.

(* TODO : delete *)
Lemma reciprocalNeg : forall (C: CField) (x: C) (xp : x [#] [0]) (nxp : ([--]x) [#] [0]),
   f_rcpcl ([--]x) nxp = [--] (f_rcpcl x xp).
Proof.
  intros ? ? ? ?.
  apply mult_cancel_lft with (z:=[--]x);[exact nxp|].
  rewrite field_mult_inv.
  rewrite inv_mult_invol.
  rewrite field_mult_inv.
  reflexivity.
Qed.

Hint Unfold One_instance_IR : IRMC.

  Lemma XAtEnd : {X (position acs)} tend =  Xs +
        ((2* Sin (θs + tc * driveDistance) 
            - Sin (θs + 2 * tc * driveDistance)  - Sin θs) [/] tc [//] tcNZ).
  Proof.
    pose proof rdriveControls as driveControlsb.
    setoid_rewrite (proj1 rsteeringControls) in driveControlsb.
    eapply  posFixedCurvX with (t:= tend) (tcNZ:=tcnegNZ _ tcNZ) in driveControlsb.
    Unshelve. Focus 2. timeReasoning.
    unfold cf_div in driveControlsb.
    rewrite θAtEnd in driveControlsb.
    rewrite reciprocalNeg with (xp:=tcNZ) in driveControlsb.
    rewrite cring_inv_mult_lft in driveControlsb.
    rewrite <- cring_inv_mult_rht in driveControlsb.
    setoid_rewrite minusInvR in driveControlsb.
    rewrite θAfterRSteer in driveControlsb.
    pose proof (csg_op_wd _ _ _ _ _ XAfterDrive driveControlsb) as Hadd.
    clear driveControlsb.
    autounfold with IRMC in Hadd.
    unfold posAtTime in rsteeringControls.
    unfold equiv, EquivCart in rsteeringControls.
    simpl in rsteeringControls.
    setoid_rewrite 
        (fun p =>  proj1 (proj1 ((proj2 rsteeringControls) trdrive p))) in Hadd;
      [|timeReasoning].
    match type of Hadd with 
    _ [=] ?r => remember r as rr
    end. 
    simpl in Hadd.
    ring_simplify in Hadd.
    rewrite Hadd. clear Hadd.  subst rr.
    autounfold with IRMC.
    unfold cf_div. unfold cg_minus. ring.
  Qed.

End Wriggle.















End Props.