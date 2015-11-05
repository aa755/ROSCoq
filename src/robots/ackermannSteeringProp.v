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

(* TODO : Move, and also delete from examples//correctness.v *)
Hint Unfold Mult_instance_TContR Plus_instance_TContR
  Negate_instance_TContR : TContR.

Section FixedSpeedFixedCurv.

  Variable tstart : Time.
  Variable tend : Time.

(* TODO : Move to MCInstances.v *)
Global Instance Le_instance_Time : Le Time := fun x y => x [<=] y.

  Hypothesis tstartEnd : (tstart ≤ tend).

  Variable tc : IR.

Open Scope mc_scope.

(** TODO: It suffices to assume it for just rational times, because of continuity *)
  Hypothesis fixed : forall (t :Time), 
    (tstart ≤ t ≤ tend)  -> {turnCurvature acs} t = tc.
  
  Local Definition θ0 := {theta acs} tstart.


  (** [theta] at time [t] is also needed obtain position at time [t] by integration *)
  Lemma fixedCurvTheta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
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

Add Ring RisaRing: (CRing_Ring IR).


  Section Positive.
  (**Needed because [tc] shows up as a denominator
     during integration below in [fixedCurvX]. The 0 case perhaps 
    needs to be handled separately, and constructively!*)
  Hypothesis tcNZ : (tc [#] 0).

  (** [X] coordinate of the [position] at a given time. Note that in CoRN,
      division is a ternary operator. [a[/]b[//][bp]] denotes the real number [a]
      divided by the non-zero real number [b], where [bp] is the proof of non-zero-hood
      of [b].
   *)
  Lemma posFixedCurvX : forall (t :Time) (_: tstart ≤ t ≤ tend),
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

  Lemma posFixedCurvY : forall (t :Time) (_: tstart ≤ t ≤ tend),
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

End Positive.

(* Now, lets get ret rid of the assumption [lvtcNZ] 

  Lemma fixedCurvX : forall (t :QTime), (tstart <= t <= tend)%Q  ->
    ({X (position acs)} t - {X (position acs)} tstart) =  
        lv * (Sin ({theta acs} tstart)).
  Proof.
  Abort.
*)

(* TODO : given the car's dimensions, confine the whole car within 
  a "small, yet simple" region
  during the above motion. *)

End FixedSpeedFixedCurv.

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

(** constant curvature of the car after (reverse) steering *)
  Variable tc : IR.
  Hypothesis tcPos : 0[<]tc.

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
  Definition rdriveDistance := ∫ driveIb (linVel acs).

  Hypothesis rdriveControls : forall (t:Time), (trdrive ≤ t ≤ tend) 
          ->  {turnCurvature acs} t = {turnCurvature acs} trdrive.

(** the distance covered during driving and reverse driving is exactly the same.
  TODO: let them be slightly different, e.g. upto epsilon
 *)
  Hypothesis driveDistanceSame : driveDistance = -rdriveDistance.


End Wriggle.


End Props.