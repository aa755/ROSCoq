Require Import Vector.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import ackermannSteering.
Require Import MCMisc.tactics.
Require Import CartIR.
Require Import fastReals.interface.
Require Import fastReals.misc.
Require Import geometry2D.
Require Import geometry2DProps.
Require Import MathClasses.orders.rings.
Require Import MathClasses.interfaces.orders.
Require Import IRMisc.LegacyIRRing.
Hint Unfold One_instance_IR : IRMC.
Require Import CartIR2.

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
Add Ring TContRisaRing: (stdlib_ring_theory TContR).

  Context  {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature).
  Variable tstart : Time.
  Variable tend : Time.
  Hypothesis timeInc : (tstart ≤ tend).

  Let dist := ∫ (mkIntBnd timeInc) (linVel acs).
  Let adist := ∫ (mkIntBnd timeInc) (CFAbs (linVel acs)).

  Lemma noChangeAbs:
  noSignChangeDuring (linVel acs) tstart tend
  -> adist = AbsIR dist.
  Proof using.
    intros.
    unfold adist, dist.
    rewrite noSignChangeAbsOfIntegral; auto.
  Qed.

  Variable tc : IR.

  Variable tcErr : IR.
(*  One step at a time .. will worry about it later.
 Variable distErr : IR. *)


  (** assume that the steering wheel is already in the right position *)
  Definition steeringAlmostFixed :=
    (∀ (t:Time), (tstart ≤ t ≤ tend)
          ->  AbsSmall tcErr (({turnCurvature acs} t) - tc)).
  (** Another useful version of the lemma could consider 2 different runs of the car
      for the same duration of the time. Both the controls (steering wheel and linVel)
      differ by atmost epsilon at all corresponding times.

      The version in this file assumes nothing about how linVel evolves,
      except that it doesnt change sign. But it assumes that steering wheel is held
      nearly constant.
      So neither of these versions is more
      general than the other.
   *)

  Hypothesis amec: steeringAlmostFixed.

(*
Local Opaque Time.
    destruct acs. simpl in *.
Local Transparent Time.

*)


(* Move *)
Lemma prodConj : forall (A B : Prop), (prod A B) ↔ (A ∧ B).
Proof using.
  intros. tauto.
Qed.

(* cant use TDerivativeAbs because the time difference is unbounded *)
  Lemma thetaBall : 
    AbsSmall
      (| tcErr * adist|)
      ({theta acs} tend - {theta acs} tstart - tc*dist) .
  Proof using timeInc amec.
    setoid_rewrite <- TBarrow with (p:=timeInc);[| apply derivRot].
    set (per  := (ContConstFun _ _ tc): TContR).
    assert (turnCurvature acs = (per + (turnCurvature acs - per))) as Heq by ring.
    rewrite Heq. clear Heq.
    rewrite plus_mult_distr_l.
    setoid_rewrite mult_comm at 2.
    setoid_rewrite CIntegral_plus. unfold per.
    unfold mult at 2. unfold Mult_instance_TContR.
    rewrite CIntegral_scale.
    fold dist.
    setoid_rewrite <- PlusShuffle3l.
    rewrite plus_negate_r, plus_0_r.
    apply AbsIR_imp_AbsSmall.
    rewrite AbsOfIntegral.
    setoid_rewrite CFAbs_resp_mult.
    rewrite IntegralMonotone with 
        (G:= (ContConstFun (closel [0]) I (AbsIR (tcErr)))*(CFAbs (linVel acs))).
  - setoid_rewrite CIntegral_scale.
    setoid_rewrite AbsIR_resp_mult.
    rewrite (AbsIR_eq_x adist);[reflexivity|].
    apply DerivNonNegIntegral.
    intros ? ?. rewrite CFAbsAp. apply AbsIR_nonneg.
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
  Qed.

  Section NZ.
  Hypothesis tcNZ : (tc [#] 0).
  Local Notation turnRadius  (* :IR *) := (f_rcpcl tc tcNZ).
  
  (** [X] coordinate of the [position] at a given time. Note that in CoRN,
      division is a ternary operator. [a[/]b[//][bp]] denotes the real number [a]
      divided by the non-zero real number [b], where [bp] is the proof of non-zero-hood
      of [b].
   *)
  Lemma fixedSteeeringX :
    let ideal := ((Sin ({theta acs} tend) - Sin ({theta acs} tstart)) [/] tc [//] tcNZ) in
    AbsSmall 
        (|tcErr * adist [/] tc [//] tcNZ|)
        (({X (position acs)} tend - {X (position acs)} tstart) - ideal).
  Proof using timeInc amec.
    simpl.
    setoid_rewrite <- TBarrow with (p:= timeInc);[| apply (derivX acs)].
    pose proof (@TContRDerivativeSin _ _ _ _ (derivRot acs)) as X.
    apply AbsIR_imp_AbsSmall.
    apply mult_cancel_leEq with (z:= (AbsIR tc));[apply AbsIR_pos; assumption | ].
    rewrite <- AbsIR_resp_mult.
    setoid_rewrite <- AbsIR_resp_mult.
    setoid_rewrite ring_distr2.
    setoid_rewrite div_1.
    rewrite (@mult_commut_unfolded IR).
    rewrite <- CIntegral_scale.
    set (per  := (ContConstFun _ _ tc): TContR).
    assert (per = (turnCurvature acs + (per - turnCurvature acs))) as Heq by ring.
    rewrite Heq. clear Heq.
    setoid_rewrite plus_mult_distr_r.
    setoid_rewrite CIntegral_plus.
    rewrite MultShuffle3l.
    rewrite mult_comm.
    rewrite TBarrow;[| apply X]. fold (CFSine (theta acs)).
    rewrite CFSineAp, CFSineAp.
    setoid_rewrite <- PlusShuffle3l.
    setoid_rewrite plus_negate_r. rewrite plus_0_r.

    (* now only the error term is left *)
    rewrite AbsOfIntegral.
    setoid_rewrite CFAbs_resp_mult.
    unfold mult, Mult_instance_TContR, Mult_instance_IR.
    rewrite CFAbs_resp_mult.
    rewrite IntegralMonotone with 
        (G:= (ContConstFun (closel [0]) I (AbsIR (tcErr)))*(CFAbs (linVel acs))).
  - setoid_rewrite CIntegral_scale.
    setoid_rewrite AbsIR_resp_mult.
    rewrite (AbsIR_eq_x adist);[reflexivity|].
    apply DerivNonNegIntegral.
    intros ? ?. rewrite CFAbsAp. apply AbsIR_nonneg.
  - intros ? Hb.
    rewrite mult_comm.
    unfold mult, Mult_instance_TContR, negate, Negate_instance_TContR, plus, Plus_instance_TContR.
    subst per.
    autorewrite with IContRApDown.
    setoid_rewrite MultShuffle3l.
    rewrite <- (@mult_assoc IR) by (eauto with typeclass_instances).
    apply mult_resp_leEq_lft;[| apply AbsIR_nonneg].
    simpl in Hb.
    apply prodConj in Hb.
    rewrite leEq_imp_Min_is_lft in Hb by assumption.
    rewrite leEq_imp_Max_is_rht in Hb by assumption.
    apply amec in Hb.
    apply AbsSmall_imp_AbsIR in Hb.
    setoid_rewrite AbsIR_minus.
    rewrite (leEq_AbsIR tcErr) in Hb.
    rewrite <- (mult_1_r (AbsIR tcErr)).
    apply mult_resp_leEq_both;
      try apply AbsIR_nonneg; auto;[].
    apply AbsIR_Cos_leEq_One.
  Qed.

  Lemma fixedSteeeringY :
    let ideal := ((Cos ({theta acs} tstart) - Cos ({theta acs} tend)) [/] tc [//] tcNZ) in
    AbsSmall 
        (|tcErr * adist [/] tc [//] tcNZ|)
        (({Y (position acs)} tend - {Y (position acs)} tstart) - ideal).
  Proof using  timeInc amec.
    simpl.
    setoid_rewrite <- TBarrow with (p:= timeInc);[| apply (derivY acs)].
    pose proof (@IContRDerivativeCos _ _ _ _ (derivRot acs)) as X.
  SearchAbout AbsSmall cr_mult.
    apply AbsIR_imp_AbsSmall.
    apply mult_cancel_leEq with (z:= (AbsIR (tc)));[apply AbsIR_pos; assumption | ].
    rewrite (AbsIR_inv tc) at 1.
    rewrite <- AbsIR_resp_mult.
    setoid_rewrite <- AbsIR_resp_mult.
    setoid_rewrite ring_distr2. unfold cg_minus.
    rewrite <- cring_inv_mult_lft.
    setoid_rewrite (@negate_involutive IR);[| eauto with typeclass_instances].
    rewrite div_1.
    setoid_rewrite div_1.
    rewrite cring_inv_mult_lft.
    rewrite <- cring_inv_mult_rht.
    unfold FSin.
    rewrite (@mult_commut_unfolded IR).
    rewrite <- CIntegral_opp.
    setoid_rewrite <-cring_inv_mult_lft.
    rewrite <- CIntegral_scale.
    set (per  := (ContConstFun _ _ tc): TContR).
    rewrite <- CartIR2.composeIContRNegate.
    assert (per = (turnCurvature acs + (per - turnCurvature acs))) as Heq by ring.
    rewrite Heq. clear Heq.
    setoid_rewrite plus_mult_distr_r.
    setoid_rewrite CIntegral_plus.
    setoid_rewrite MultShuffle3l.
    rewrite mult_comm.
    rewrite TBarrow; [| apply X]. fold (CFCos (theta acs)).
    do 2 rewrite CFCosAp.
    setoid_rewrite <- PlusShuffle3l.
    rewrite (@negate_swap_r IR _ _ _ _ _ _ _ _) at 1.
    setoid_rewrite plus_negate_r. rewrite plus_0_r.

    (* now only the error term is left *)
    rewrite AbsOfIntegral.
    setoid_rewrite CFAbs_resp_mult.
    change ((linVel acs * (per - turnCurvature acs))) 
      with ( (linVel acs [*] (per - turnCurvature acs))).
    rewrite CFAbs_resp_mult.
    rewrite IntegralMonotone with 
        (G:= (ContConstFun (closel [0]) I (AbsIR (tcErr)))*(CFAbs (linVel acs))).
  - setoid_rewrite CIntegral_scale.
    setoid_rewrite AbsIR_resp_mult.
    rewrite (AbsIR_eq_x adist);[reflexivity|].
    apply DerivNonNegIntegral.
    intros ? ?. rewrite CFAbsAp. apply AbsIR_nonneg.
  - intros ? Hb.
    rewrite mult_comm.
    unfold mult, Mult_instance_TContR, negate, Negate_instance_TContR, plus, Plus_instance_TContR.
    subst per.
    autorewrite with IContRApDown.
    rewrite <- (@mult_assoc_unfolded IR).
    apply mult_resp_leEq_lft;[| apply AbsIR_nonneg].
    simpl in Hb.
    apply prodConj in Hb.
    rewrite leEq_imp_Min_is_lft in Hb by assumption.
    rewrite leEq_imp_Max_is_rht in Hb by assumption.
    apply amec in Hb.
    apply AbsSmall_imp_AbsIR in Hb.
    setoid_rewrite AbsIR_minus in Hb.
    rewrite (leEq_AbsIR tcErr) in Hb.
    rewrite <- (mult_1_r (AbsIR tcErr)).
    apply mult_resp_leEq_both;
      try apply AbsIR_nonneg; auto;[].
    rewrite CartIR2.composeIContRNegate.
    fold (CFCos (theta acs)).
    autorewrite with IContRApDown.
    rewrite <- AbsIR_inv.
    fold (CFSine (theta acs)).
    setoid_rewrite CFSineAp.
    apply AbsIR_Sin_leEq_One.
  Qed.



  End NZ.

  Check FCos.

  (* generalize and move *)
  Global Instance ProperFCos (I : interval) (pI : proper I) :
    Proper (equiv ==> equiv) (@FCos I pI).
  Admitted.

(* is there an automatic way (internal or via tactic) to lift lemmas about
Cos to lemmas about FCos? *)
Lemma FCos_plus: ∀ x y : TContR (* IContR*),
   FCos (x + y) = FCos x * FCos y - FSin x * FSin y.
Admitted.


  Lemma AtomicMoveZX :
    let ideal := (∫ (mkIntBnd timeInc) (linVel acs)) * (Cos tstart)  in
    AbsSmall 0
      ({X (position acs)} tend - {X (position acs)} tstart
        - ideal).
  Proof using.
    simpl.
    rewrite mult_comm.
    setoid_rewrite <- TBarrow with (p := timeInc);
      [| apply derivX].
    set (per := (ContConstFun _ _ ({theta acs} tstart)):TContR).
    assert (theta acs = theta acs - per + per) as Heq by ring.
    rewrite Heq.
    rewrite FCos_plus.
    (* use this instead for per? *)
    set (per2 := (ContConstFun _ _ (Cos ({theta acs} tstart))):TContR).
  Abort.

(*  End Car. *)

(*
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
*)

End Car.



