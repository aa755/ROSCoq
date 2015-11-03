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

  (**Needed because [lv * tc] shows up as a denominator
     during integration. The 0 case perhaps 
    needs to be handled separately, and constructively!*)
  Hypothesis lvtcNZ : (lv * tc [#] 0).

  Hypothesis fixed : forall (t :QTime), 
    (tstart <= t <= tend)%Q  -> {linVel acs} t = lv /\ {turnCurvature acs} t = tc.
  
  Lemma tcNZ : (tc [#] 0).
  Proof.
    apply mult_cancel_ap_zero_rht in lvtcNZ.
    exact lvtcNZ.
  Qed.

  Lemma lvNZ : (lv [#] 0).
  Proof.
    apply mult_cancel_ap_zero_lft in lvtcNZ.
    exact lvtcNZ.
  Qed.

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

  (** [X] coordinate of the [position] at a given time. Note that in CoRN,
      division is a ternary operator. [a[/]b[//][bp]] denotes the real number [a]
      divided by the non-zero real number [b], where [bp] is the proof of non-zero-hood
      of [b].
   *)
  Lemma fixedCurvX : forall (t :QTime), (tstart <= t <= tend)%Q  ->
    ({X (position acs)} t - {X (position acs)} tstart) =  
        ((Sin ({theta acs} t) [-] Sin ({theta acs} tstart)) [/] tc [//] tcNZ) (* temporary placeholder *).
  Proof.
    intros ? Hb.
    pose proof (TBarrowQScale _ _ (FCos (theta acs)) (derivX acs) tstart t lv (proj1 Hb)) as Dx.
    rewrite Dx;
    [ |intros tb Hbb; autounfold with TContRMC; autorewrite with IContRApDown;
       apply mult_wdl; apply fixed; lra].
    rewrite (Cintegral_wd2).
    instantiate (1 := FCos (ContConstFun _ _ (θ0 - lv * tc * (Q2R tstart)) 
                          + ContConstFun  _ _ (lv * tc) * IContRId _ _)).
    Focus 2.
      apply EqRationalCont.
      intros tb Hbb. rewrite CFCosAp, CFCosAp.
      apply Cos_wd.
      apply fixedCurvTheta2. lra.
      
    unfold CFCos. setoid_rewrite IContRIntegLinearCos2 with (p:=lvtcNZ).
    match goal with 
    [ |-  context [?l [-] ?r ]] => remember (l [-] r)
    end. unfold cf_div.
    setoid_rewrite f_rcpcl_mult with (y_ := lvNZ) (z_ := tcNZ).
    assert (lv [*] (s [*] (f_rcpcl lv lvNZ [*] f_rcpcl tc tcNZ)) [=]
                (lv [*]f_rcpcl lv lvNZ) [*] s [*] (f_rcpcl tc tcNZ)) as Hr by ring.
    rewrite Hr. clear Hr. rewrite field_mult_inv. rewrite one_mult.
    apply div_wd;[| reflexivity]. subst s.
    setoid_rewrite <- fixedCurvTheta2;[ | lra | lra]. reflexivity.
Qed.

    
End FixedSpeedFixedCurv.

End Props.