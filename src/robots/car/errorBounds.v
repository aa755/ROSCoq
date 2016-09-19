Require Import Vector.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import ackermannSteering.
Require Import MCMisc.tactics.
Require Import CartIR.
Require Import ackermannSteering.
Require Import fastReals.interface.
Require Import fastReals.misc.
Require Import geometry2D.
Require Import geometry2DProps.
Require Import ackermannSteeringProp.
Require Import MathClasses.orders.rings.
Require Import MathClasses.interfaces.orders.
Require Import atomicMoves.
Require Import IRMisc.LegacyIRRing.
Require Import wriggle.
Hint Unfold One_instance_IR : IRMC.

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
Local Opaque Min Max.

Require Import CoRN.metric2.Metric.
Require Import CRMisc.OldMetricAsNew.
Require Import MCMisc.rings.
Require Import MathClasses.theory.rings.
Let rball : Qpos → IR → IR → Prop  :=
@ball (fromOldMetricTheory IR_as_CMetricSpace). 


Section Car.
  Context  {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature).
  Variable tstart : Time.
  Variable tend : Time.
  Hypothesis nsc : noSignChangeDuring (linVel acs) tstart tend.

  Variable am : AtomicMove IR.
  Section Drive.

  Variable tcErr : IR.
(*  One step at a time .. will worry about it later.
 Variable distErr : IR. *)

  Hypothesis timeInc : (tstart ≤ tend).

  (* assume that the steering wheel is already in the right position *)
  Definition amExecDirect :=
    (∀ (t:Time), (tstart ≤ t ≤ tend)
          ->  AbsSmall tcErr (({turnCurvature acs} t) - (am_tc am))) ∧
    (let driveIb := (@mkIntBnd _ tstart tend timeInc) in
         (∫ driveIb (linVel acs)) = (am_distance am)).

  Hypothesis ame: amExecDirect.

(*
Local Opaque Time.
    destruct acs. simpl in *.
Local Transparent Time.

*)

Add Ring TContRisaRing: (stdlib_ring_theory TContR).

(* Move *)
Lemma prodConj : forall (A B : Prop), (prod A B) ↔ (A ∧ B).
Proof using.
  intros. tauto.
Qed.


(* cant use TDerivativeAbs because the time difference is unbounded *)
  Lemma thetaBall : 
           AbsSmall
             (| tcErr * (am_distance am)|)
             ({theta acs} tend - {theta acs} tstart
                        -(am_tc am)*(am_distance am)) .
  Proof using timeInc nsc ame.
    destruct ame as [amec amed]. simpl.
    setoid_rewrite <- TBarrow with (p:=timeInc);[| apply derivRot].
    set (per  := (ContConstFun _ _ (am_tc am)): TContR).
    assert (turnCurvature acs = (per + (turnCurvature acs - per))) as Heq by ring.
    rewrite Heq. clear Heq.
    rewrite plus_mult_distr_l.
    setoid_rewrite mult_comm at 2.
    setoid_rewrite CIntegral_plus. unfold per.
    unfold mult at 2. unfold Mult_instance_TContR.
    rewrite CIntegral_scale.
    rewrite amed.
    setoid_rewrite <- PlusShuffle3l.
    rewrite plus_negate_r, plus_0_r.
    apply AbsIR_imp_AbsSmall.
    eapply transitivity;[apply AbsOfIntegral|].
    setoid_rewrite CFAbs_resp_mult.
    eapply transitivity.
    apply IntegralMonotone with 
        (G:= (ContConstFun (closel [0]) I (AbsIR (tcErr)))*(CFAbs (linVel acs))).
  - intros ? Hb.
    rewrite mult_comm.
    unfold mult, Mult_instance_TContR, negate, Negate_instance_TContR, plus, Plus_instance_TContR.
    autorewrite with IContRApDown.
    apply mult_resp_leEq_lft;[| apply AbsIR_nonneg].
    simpl in Hb.
    apply prodConj in Hb.
    rewrite leEq_imp_Min_is_lft in Hb by assumption.
    rewrite leEq_imp_Max_is_rht in Hb by assumption.
    apply amec in Hb.
    apply AbsSmall_imp_AbsIR in Hb.
    eapply transitivity; eauto using leEq_AbsIR.
  - setoid_rewrite CIntegral_scale.
    rewrite noSignChangeAbsOfIntegral by assumption.
    rewrite amed.
    rewrite <- AbsIR_resp_mult.
    reflexivity.
  Qed.

(*
ackermannSteeringProp.fixedSteeeringX
*)


  End Drive.

  Section AtomicMove.
  

  Variable tcErr : Qpos.
  Variable distErr : Qpos.
   

  Set Implicit Arguments.
  (** This defines what it means for the car's controls to 
    realistically follow the atomic move [am] during time [tstart] to [tend] *)
  Record CarExecutesAtomicMoveDuring (p: tstart < tend) : Type :=
  {
    am_tdrive : Time;

    (**strict inequalities prevents impossilities like covering non-zero distance in 0 time.
      Note that [linVel] and [turnCurvature] evolve continuously.
     *)
    am_timeInc : (tstart < am_tdrive < tend);
 
  (** From time [tsteer] to [drive], the steerring wheel rotates to attain a configuration 
    with turn curvature [tc]. The brakes are firmly placed pressed.*)
    am_steeringControls : rball tcErr ({turnCurvature acs} am_tdrive)  (am_tc am) 
      /\ forall (t:Time), (tstart ≤ t ≤ am_tdrive) 
          -> {linVel acs} t = 0;

 
  (** From time [tdrive] to [tend], the steering wheel is held NEARLY fixed*)
    am_driveControls : forall (t:Time), (am_tdrive ≤ t ≤ tend) 
          ->  rball tcErr ({turnCurvature acs} t) (am_tc am);
          
   am_driveDistance : 
      let pf := (timeLtWeaken (proj2 (am_timeInc))) in 
      let driveIb := (@mkIntBnd _ am_tdrive tend pf) in 
         rball distErr (am_distance am)  (∫ driveIb (linVel acs))
  }.

End AtomicMove.
End Car.



