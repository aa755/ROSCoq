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

(*
  Lemma ss (x: Cart2D IR) : x ≤ x.
  Lemma ss (x: Rigid2DState IR) : x ≤ x. *)

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

  Definition turnRigidStateAtDist (init : Rigid2DState IR)
  (tc: sigT (fun a => apartT a (0:IR))) (d : IR) :
    Rigid2DState IR
  := 
  let tr :IR := recipT (projT1 tc) (projT2 tc) in
  let θi := θ2D init in
  let θ :IR := θi + (projT1 tc)*d in
  turnRigidStateAtθ init tr θ.

Section Car.
Add Ring TContRisaRing: (stdlib_ring_theory TContR).

  Context  {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature).
  Section Turn.
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

  Hypothesis tcNZ : (tc [#] 0).

  Local Notation turnRadius  (* :IR *) := (f_rcpcl tc tcNZ).
  
  (** [X] coordinate of the [position] at a given time. Note that in CoRN,
      division is a ternary operator. [a[/]b[//][bp]] denotes the real number [a]
      divided by the non-zero real number [b], where [bp] is the proof of non-zero-hood
      of [b].

    Note that the error scales linearly with turn radius.
    So this is not a good characterization
    for driving (nearly) straight.
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

Typeclasses eauto :=4.

(*
  Lemma fixedSteeeringTurn :
  let rs:= rigidStateAtTime acs in
  let tcc := (existT _ tc tcNZ) in
    pNorm (rs tend - 
            (turnRigidStateAtDist (rs tstart) tcc dist))
    ≤ {| pos2D := '(|tcErr * adist [/] tc [//] tcNZ|); θ2D := (| tcErr * adist|)|}.
  Proof.
    unfold turnRigidStateAtDist, recipT, RecipTIR.
    simpl. split;  simpl;[split;simpl|]; apply AbsSmall_imp_AbsIR.
  - Fail apply fixedSteeeringX. admit.
  - rewrite negate_plus_distr.
    setoid_rewrite (@simple_associativity IR _ plus _ _ _ _).
Fail apply fixedSteeeringY.

Doesn't work!! Now, angle at tend is not known exactly. So turnRigidStateAtDist
doesn't work. use turnRigidStateAtθ instead.


  - rewrite negate_plus_distr.
    setoid_rewrite (@simple_associativity IR _ plus _ _ _ _).
    apply thetaBall.
Qed.
*)

  Lemma fixedSteeeringTurn :
  let rs:= rigidStateAtTime acs in
    pNorm (rs tend - 
            (turnRigidStateAtθ (rs tstart) turnRadius ({theta acs} tend)))
    ≤ {| pos2D := '(|tcErr * adist [/] tc [//] tcNZ|); θ2D := (| tcErr * adist|)|}.
  Proof.
    unfold turnRigidStateAtDist, recipT, RecipTIR.
    simpl. split;  simpl;[split;simpl|]; apply AbsSmall_imp_AbsIR; simpl;
    try (rewrite negate_plus_distr;
    setoid_rewrite (@simple_associativity IR _ plus _ _ _ _));
    try apply fixedSteeeringX;
    try apply fixedSteeeringY;[].
    rewrite plus_negate_r.
    apply zero_AbsSmall. apply AbsIR_nonneg.
  Qed.
  Lemma holdsDuringAMIf : forall(P: (Rigid2DState IR) -> Prop)
    `{@Setoid_Morphism  _ _ _ _ P},
  let θs := ({theta acs} tstart) in 
    noSignChangeDuring (linVel acs) tstart tend
    ->
    (∀ θe, AbsSmall (| tcErr * adist|)  (θe - (θs + tc*dist)) (* remove this quantif to get 1 range *)
        ->
       ∀ (θ : IR), inBetweenR θ θs θe
      -> P (turnRigidStateAtθ (rigidStateAtTime acs tstart) turnRadius θ))
     ->  (∀ t : Time, tstart ≤ t ≤ tend → P (rigidStateAtTime acs t)).
  Abort.

  (* move to outside the section so that t can be used instead of tend*)
  Lemma holdsDuringAMIf : forall(P: (Rigid2DState IR) -> Prop)
    `{@Setoid_Morphism  _ _ _ _ P},
    let θs := ({theta acs} tstart) in 
    let θe := θs + tc*dist in 
    let θerr := (| tcErr * adist|) in 
    noSignChangeDuring (linVel acs) tstart tend
    ->
    (∀ (θ : IR), (Min θs (θe - θerr) [<=] θ ∧ θ [<=] Max θs (θe + θerr))
      -> P (turnRigidStateAtθ (rigidStateAtTime acs tstart) turnRadius θ))
     ->  (∀ t : Time, tstart ≤ t ≤ tend → P (rigidStateAtTime acs t)).
  Proof. simpl.
    intros ? ?  Hn hh t Hb.
    specialize (hh ({theta acs}t)).
  Abort.

  End Turn.

(* we need the intermediate values of theta. Unless we end the section
  and force generalization, we only have [theta] for [tend]. *)

  Section Straight.
  Variable tstart : Time.
  Variable tend : Time.
  Hypothesis timeInc : (tstart ≤ tend).

  Let dist := ∫ (mkIntBnd timeInc) (linVel acs).
  Let adist := ∫ (mkIntBnd timeInc) (CFAbs (linVel acs)).


  Variable tcErr : IR.
(*  One step at a time .. will worry about it later.
 Variable distErr : IR. *)


  Hypothesis amec: steeringAlmostFixed tstart tend 0 tcErr.



  (* generalize and move *)
  Global Instance ProperFCos (I : interval) (pI : proper I) :
    Proper (equiv ==> equiv) (@FCos I pI).
  Abort.

(* is there an automatic way (internal or via tactic) to lift lemmas about
Cos to lemmas about FCos? *)
Lemma FCos_plus: ∀ x y : TContR (* IContR*),
   FCos (x + y) = FCos x * FCos y - FSin x * FSin y.
Abort.

(* Move *)
  Local Transparent CSine CCos.
Lemma CSineAp x : {CSine} x = Sin x.
Proof using.
  simpl. apply SineSin.
Qed.

Lemma CCosAp x : {CCos} x = Cos x.
Proof using.
  simpl. apply CosineCos.
Qed.

Hint Rewrite CSineAp CCosAp : IContRApDown.

(* Move *)

Lemma SineLe (x:IR): 
  0 [<=] x ->  (Sin x)  [<=] x.
Proof using.
  intro Hn.
  pose proof (TBarrow 
                (IsDerivativeOne realline I)
                {|scs_elem:=0; scs_prf:=I|} 
                {|scs_elem:=x; scs_prf:=I|} Hn) as Hone.
  pose proof (TBarrow 
                IsDerivativeCos
                {|scs_elem:=0; scs_prf:=I|} 
                {|scs_elem:=x; scs_prf:=I|} Hn) as Hc.
  autorewrite with IContRApDown in *.

  Local Opaque cg_inv cr_one.
  simpl in *.
  simpl in Hc.
  rewrite Sin_zero in Hc.
  setoid_rewrite minus_0_r in Hone.
  setoid_rewrite minus_0_r in Hc.
  rewrite <- Hc.
  rewrite <- Hone at 2.
  apply IntegralMonotone.
  intros ? ? . simpl. rewrite CosineCos.
  apply Cos_leEq_One.
Qed.

Lemma Cos_leEq_minus_one r : [--] [1] [<=] Cos r.
Proof using.
  pose proof (AbsIR_Cos_leEq_One r) as Hl.
  apply AbsIR_imp_AbsSmall in Hl.
  apply Hl.
Qed.


Lemma NegSineLe (x:IR): 
  0 [<=] x ->  -(Sin x)  [<=] x.
Proof using.
  intro Hn.
  pose proof (TBarrow 
                (IsDerivativeOne realline I)
                {|scs_elem:=0; scs_prf:=I|} 
                {|scs_elem:=x; scs_prf:=I|} Hn) as Hone.
  pose proof IsDerivativeCos as Hcc.
  apply TContRDerivativeOpp in Hcc.
  pose proof (TBarrow 
                Hcc
                {|scs_elem:=0; scs_prf:=I|} 
                {|scs_elem:=x; scs_prf:=I|} Hn) as Hc.
  autorewrite with IContRApDown in *.
  simpl in *.
  rewrite Sin_zero in Hc.
  setoid_rewrite negate_0 in Hc.
  setoid_rewrite minus_0_r in Hone.
  setoid_rewrite minus_0_r in Hc.
  rewrite <- Hc.
  rewrite <- Hone at 2.
  apply IntegralMonotone.
  intros ? ? .
  autorewrite with IContRApDown.
  Local Transparent cr_one.
 simpl.
  apply inv_cancel_leEq.
  setoid_rewrite negate_involutive.
  apply Cos_leEq_minus_one.
Qed.

Lemma AbsSineLe (x:IR): 
  0 [<=] x -> AbsIR (Sin x)  [<=] x.
Proof using.
  intros Hn.
  apply stable.
  pose proof (leEq_or_leEq _ 0 (Sin x)) as Hdec.
  eapply Stability.DN_fmap; eauto.
  clear Hdec. intros Hdec.
  destruct Hdec as [Hdec | Hdec].
- rewrite (AbsIR_eq_x) by assumption.
  apply SineLe. assumption.
- rewrite (AbsIR_eq_inv_x) by assumption.
  apply NegSineLe. assumption.
Qed.
  

Lemma sineAbsXLe (x:IR): AbsIR (Sin x)  [<=] AbsIR x.
Proof using.
  apply stable.
  pose proof (leEq_or_leEq _ 0 x) as Hdec.
  eapply Stability.DN_fmap; eauto.
  clear Hdec. intros Hdec.
  destruct Hdec as [Hdec | Hdec].
- rewrite (AbsIR_eq_x x) by assumption.
  apply  AbsSineLe. assumption.
- rewrite (AbsIR_eq_inv_x x) by assumption.
  eapply transitivity;
    [ | eapply AbsSineLe;
    setoid_rewrite <- flip_nonpos_negate; assumption].
  rewrite Sin_inv, <- AbsIR_inv.
  reflexivity.
Qed.

Local Opaque Half.

(* Move *)
Lemma minus_cos : ∀ x y : IR,
   Cos x - Cos y = 
    - Two * Sin (Half * (x - y)) [*] Sin (Half * (x + y)).
Proof using.
  clear.
  intros.
  set (u:=Half*(x+y)).
  set (v:=Half*(x-y)).
  assert (Half * (x + y) + Half * (x - y) =
          Half*Two*x) as Heq by IRring.
  setoid_rewrite half_1 in Heq.
  setoid_rewrite mult_1_l in Heq.
  
  assert (Half * (x + y) - Half * (x - y) =
          Half*Two*y) as Heqy by IRring.
  setoid_rewrite half_1 in Heqy.
  setoid_rewrite mult_1_l in Heqy.
  rewrite <- Heq. rewrite <- Heqy at 3.
  unfold u,v.
  autounfold with IRMC.
  rewrite Cos_plus.
  rewrite Cos_plus.
  repeat rewrite Cos_inv.
  repeat rewrite Sin_inv.
  autounfold with IRMC.
  IRring.
Qed.

(* Move *)
Lemma minus_sin : ∀ x y : IR,
   Sin x - Sin y = 
     Two * Sin (Half * (x - y)) [*] Cos (Half * (x + y)).
Proof using.
  clear.
  intros.
  set (u:=Half*(x+y)).
  set (v:=Half*(x-y)).
  assert (Half * (x + y) + Half * (x - y) =
          Half*Two*x) as Heq by IRring.
  setoid_rewrite half_1 in Heq.
  setoid_rewrite mult_1_l in Heq.
  
  assert (Half * (x + y) - Half * (x - y) =
          Half*Two*y) as Heqy by IRring.
  setoid_rewrite half_1 in Heqy.
  setoid_rewrite mult_1_l in Heqy.
  rewrite <- Heq. rewrite <- Heqy at 3.
  unfold u,v.
  autounfold with IRMC.
(* only the next 2 lines were changed w.r.t minus_cos *)
  rewrite Sin_plus.
  rewrite Sin_plus.
  repeat rewrite Cos_inv.
  repeat rewrite Sin_inv.
  autounfold with IRMC.
  IRring.
Qed.

  Lemma thetaBallInter (r:Time)  (Hb : tstart [<=] r ∧ r [<=] tend):
    AbsIR ({theta acs} r - {theta acs} tstart) 
    [<=] AbsIR (tcErr [*] adist).
  Proof.
    pose proof (thetaBall _ _ (proj1 Hb) 0 tcErr) as Ht.
    rewrite mult_0_l, minus_0_r in Ht.
    (* tc=0 was not used above. *)
    lapply Ht;
     [ | intros ? ?; apply amec; split; try tauto;
         repnd; eapply transitivity; eauto].
    clear Ht. intro Ht.
    apply AbsSmall_imp_AbsIR in Ht.
    eapply transitivity; eauto.
    setoid_rewrite AbsIR_resp_mult.
    apply mult_resp_leEq_lft;[| apply AbsIR_nonneg].
    unfold adist.
    do 2 (rewrite AbsIR_eq_x;
      [| apply DerivNonNegIntegral; 
         intros ? ?; rewrite CFAbsAp; apply AbsIR_nonneg]).
    rewrite CintegralSplit with (pl := (proj1 Hb)) (pr := (proj2 Hb)).
    apply RingLeProp1l.
    apply DerivNonNegIntegral; 
         intros ? ?; rewrite CFAbsAp; apply AbsIR_nonneg.
  Qed.
    
(* this lemma is different from the work in iCreate beause here there
   is no dependence on the duration of motion. there, there was a dependence.
  There, the linear velocity was nearly constant. Here we are making 
  no such assumption *)

  Lemma AtomicMoveZX :
    let ideal := (∫ (mkIntBnd timeInc) (linVel acs)) * (Cos ({theta acs} tstart))  in
    AbsSmall ( (|tcErr|) * sqr (adist))
      ({X (position acs)} tend - {X (position acs)} tstart
        - ideal).
  Proof using amec.
    simpl. remember ((| tcErr |) * sqr adist) as errb.
    rewrite mult_comm.
    setoid_rewrite <- TBarrow with (p := timeInc);
      [| apply derivX].
    set (per := (ContConstFun _ _ (Cos ({theta acs} tstart))):TContR).
    set (fc:=FCos (theta acs):TContR).
    assert (fc  = fc - per + per) as Heq by ring.
    rewrite Heq. clear Heq.
    rewrite plus_mult_distr_l.
    setoid_rewrite mult_comm at 2.
    setoid_rewrite CIntegral_plus. unfold per.
    unfold mult at 2. unfold Mult_instance_TContR.
    rewrite CIntegral_scale.
    fold dist.
    setoid_rewrite RingProp2.
  (* now only the error term is left *)
    apply AbsIR_imp_AbsSmall.
    rewrite AbsOfIntegral.
    setoid_rewrite CFAbs_resp_mult.
    rewrite IntegralMonotone with 
        (G:= (ContConstFun (closel [0]) I (AbsIR (tcErr * adist)))
              * (CFAbs (linVel acs))).
  - setoid_rewrite CIntegral_scale. fold adist.
    subst errb. apply eq_imp_leEq.
    setoid_rewrite AbsIR_resp_mult. unfold sqr, norm, NormSpace_instance_IR.
    rewrite (AbsIR_eq_x adist);[IRring|].
    apply DerivNonNegIntegral.
    intros ? ?. rewrite CFAbsAp. apply AbsIR_nonneg.
  - intros ? Hb.
    rewrite mult_comm.
    unfold fc.
    unfold mult, Mult_instance_TContR, negate, Negate_instance_TContR, 
      plus, Plus_instance_TContR, Mult_instance_IR.
    autorewrite with IContRApDown.
    remember (tcErr [*] adist) as rhs.
    apply mult_resp_leEq_lft;[| apply AbsIR_nonneg].
    simpl in Hb.
    apply prodConj in Hb.
    rewrite leEq_imp_Min_is_lft in Hb by assumption.
    rewrite leEq_imp_Max_is_rht in Hb by assumption.
    setoid_rewrite minus_cos.
    do 1 setoid_rewrite AbsIR_resp_mult.
    rewrite <- (mult_1_r (AbsIR rhs)).
    apply mult_resp_leEq_both;
      try apply AbsIR_nonneg; auto;[| apply AbsIR_Sin_leEq_One].
    do 1 setoid_rewrite AbsIR_resp_mult.
    setoid_rewrite <- AbsIR_inv.
    eapply transitivity;
      [apply mult_resp_leEq_lft;[apply sineAbsXLe| apply AbsIR_nonneg] | ].
    do 1 setoid_rewrite AbsIR_resp_mult.
    rewrite AbsIR_eq_x;[| apply less_leEq, pos_two].
    rewrite AbsIR_eq_x;[| apply less_leEq, pos_half].
    rewrite mult_assoc_unfolded.
    setoid_rewrite mult_commut_unfolded at 2.
    rewrite half_1. setoid_rewrite mult_1_l.
    subst rhs.
    apply thetaBallInter. assumption.
  Qed.

  Lemma AtomicMoveZY :
    let ideal := (∫ (mkIntBnd timeInc) (linVel acs)) 
                  * (Sin ({theta acs} tstart))  in
    AbsSmall ( (|tcErr|) * sqr (adist))
      ({Y (position acs)} tend - {Y (position acs)} tstart
        - ideal).
  Proof using amec.
    simpl. remember ((| tcErr |) * sqr adist) as errb.
    rewrite mult_comm.
    setoid_rewrite <- TBarrow with (p := timeInc);
      [| apply derivY].
    set (per := (ContConstFun _ _ (Sin ({theta acs} tstart))):TContR).
    set (fc:=FSin (theta acs):TContR).
    assert (fc  = fc - per + per) as Heq by ring.
    rewrite Heq. clear Heq.
    rewrite plus_mult_distr_l.
    setoid_rewrite mult_comm at 2.
    setoid_rewrite CIntegral_plus. unfold per.
    unfold mult at 2. unfold Mult_instance_TContR.
    rewrite CIntegral_scale.
    fold dist.
    setoid_rewrite RingProp2.
  (* now only the error term is left *)
    apply AbsIR_imp_AbsSmall.
    rewrite AbsOfIntegral.
    setoid_rewrite CFAbs_resp_mult.
    rewrite IntegralMonotone with 
        (G:= (ContConstFun (closel [0]) I (AbsIR (tcErr * adist)))
              * (CFAbs (linVel acs))).
  - setoid_rewrite CIntegral_scale. fold adist.
    subst errb. apply eq_imp_leEq.
    setoid_rewrite AbsIR_resp_mult. unfold sqr, norm, NormSpace_instance_IR.
    rewrite (AbsIR_eq_x adist);[IRring|].
    apply DerivNonNegIntegral.
    intros ? ?. rewrite CFAbsAp. apply AbsIR_nonneg.
  - intros ? Hb.
    rewrite mult_comm.
    unfold fc.
    unfold mult, Mult_instance_TContR, negate, Negate_instance_TContR, 
      plus, Plus_instance_TContR, Mult_instance_IR.
    autorewrite with IContRApDown.
    remember (tcErr [*] adist) as rhs.
    apply mult_resp_leEq_lft;[| apply AbsIR_nonneg].
    simpl in Hb.
    apply prodConj in Hb.
    rewrite leEq_imp_Min_is_lft in Hb by assumption.
    rewrite leEq_imp_Max_is_rht in Hb by assumption.
    setoid_rewrite minus_sin.
    do 1 setoid_rewrite AbsIR_resp_mult.
    rewrite <- (mult_1_r (AbsIR rhs)).
    apply mult_resp_leEq_both;
      try apply AbsIR_nonneg; auto;[| apply AbsIR_Cos_leEq_One].
    do 1 setoid_rewrite AbsIR_resp_mult.
    eapply transitivity;
      [apply mult_resp_leEq_lft;[apply sineAbsXLe| apply AbsIR_nonneg] | ].
    do 1 setoid_rewrite AbsIR_resp_mult.
    rewrite AbsIR_eq_x;[| apply less_leEq, pos_two].
    rewrite AbsIR_eq_x;[| apply less_leEq, pos_half].
    rewrite mult_assoc_unfolded.
    setoid_rewrite mult_commut_unfolded at 2.
    rewrite half_1. setoid_rewrite mult_1_l.
    subst rhs.
    apply thetaBallInter. assumption.
  Qed.

End Straight.


End Car.



