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

Section Props.
Variable maxTurnCurvature : Qpos.
Variable acs : AckermannCar maxTurnCurvature.


(** 
We characterize the motion of a car at a particular fixed speed, and
at a particular fixed turn curvature.
Ideally, we should let both of them vary a bit (upto some epsilon) during the process.
*)

(* TODO : Move, and also delete from examples//correctness.v *)
Hint Unfold Mult_instance_TContR Plus_instance_TContR
  Negate_instance_TContR : TContR.

Section FixedSpeedFixedCurv.
  Variable tstart : QTime.
  Variable tend : QTime.

  Hypothesis tstartEnd : (tstart <= tend)%Q.

  Variable lv : IR.
  Variable tc : IR.

  Hypothesis fixed : forall (t :QTime), 
    (tstart <= t <= tend)%Q  -> {linVel acs} t = lv /\ {turnCurvature acs} t = tc.
  
  Local Definition θ0 := {theta acs} tstart.

  (** [theta] at time [t] is also needed obtain position at time [t] by integration *)
  Lemma fixedCurvTheta : forall (t :QTime), (tstart <= t <= tend)%Q  ->
    ({theta acs} t - {theta acs} tstart) = lv * tc * (Q2R (t - tstart)).
  Proof.
    intros ? Hb.  
    eapply TDerivativeEqQ; eauto using derivRot;[lra|].
    intros tb Hbb.
    assert (tstart <= tb <= tend)%Q as Hbbb by lra.
    clear Hb Hbb. rename Hbbb into Hb.
    apply fixed in Hb. repnd.
    autounfold with TContRMC.
    autounfold with IRMC. simpl.
    rewrite Hbl, Hbr. reflexivity.
  Qed.

Add Ring RisaRing: (CRing_Ring IR).

  (** put the above in a form that is more convenient for integrating it
      while computing the X and Y coordinates at a given time *)
  Lemma fixedCurvTheta2 : forall (t :QTime), (tstart <= t <= tend)%Q  ->
    ({theta acs} t) =  {ContConstFun _ _ (θ0 - lv * tc * (Q2R tstart)) 
                          + ContConstFun  _ _ (lv * tc) * IContRId _ _} t.
  Proof.
    intros ? H. autounfold with TContRMC. autounfold with IRMC.
    simpl.
    apply fixedCurvTheta in H.
    rewrite <- (realCancel _  ({theta acs} t) θ0).
    fold θ0. rewrite H.
    unfold Q2R. autorewrite with InjQDown.
    unfold cg_minus. rewrite <- QT2T_Q2R. simpl.
    autounfold with IRMC.
    ring.
  Qed.

  (** [theta] at time [t] is also needed obtain position at time [t] by integration *)
  Lemma fixedCurvX : forall (t :QTime), (tstart <= t <= tend)%Q  ->
    ({X (position acs)} t - {X (position acs)} tstart) = lv * 0 (* temporary placeholder *).
  Proof.
    intros ? Hb.
    pose proof (TBarrowQScale _ _ (FCos (theta acs)) (derivX acs) tstart t lv (proj1 Hb)) as Dx.
    rewrite Dx;
    [ |intros tb Hbb; autounfold with TContRMC; autorewrite with IContRApDown;
       apply mult_wdl; apply fixed; lra].
    apply mult_wdr.
    rewrite Cintegral_wd2.
    Focus 2.
    Print Cintegral.
    Print CFSine.
    SearchAbout integral Sine.
    intros tx HH. unfold inBounds in HH. simpl in HH.
    SearchAbout Sine.    
    Print TBarrowQ.
    SearchAbout isIDerivativeOf.
    SearchAbout Integral.
  Abort.

    
End FixedSpeedFixedCurv.

End Props.