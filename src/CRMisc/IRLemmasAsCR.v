
Require Export CoRN.reals.fast.CRtrans.
(* Require Export CoRN.reals.faster.ARbigD. *)
(* Require Export CoRN.ftc.IntegrationRules. *)

Require Export Coq.Program.Tactics.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.
Require Export MathClasses.interfaces.abstract_algebra.
Require Export CoRN.transc.PowerSeries.
Require Export CoRN.transc.Pi.
Require Export CoRN.transc.TrigMon.
Require Export CoRN.transc.MoreArcTan.
Require Export CoRN.transc.Exponential.
Require Export CoRN.transc.InvTrigonom.
Require Export CoRN.transc.RealPowers.
Require Export CoRN.transc.Trigonometric.
Require Export CoRN.transc.TaylorSeries.


Instance Injective_instance_CRasIR : Injective  CRasIR.
  constructor.
- intros ? ? Heq. apply (fun_strext_imp_wd _ _ IRasCR) in Heq;
    [ | apply R_morphism.map_strext].
  repeat( rewrite CRasIRasCR_id in Heq).
  exact Heq.
- constructor;eauto 2 with *.
  exact CRasIR_wd.
Qed.

Instance Injective_instance_IRasCR : Injective  IRasCR.
  constructor.
- intros ? ? Heq. apply (fun_strext_imp_wd _ _ CRasIR) in Heq;
    [ | apply R_morphism.map_strext].
  repeat (rewrite IRasCRasIR_id in Heq).
  exact Heq.
- constructor; try apply st_isSetoid.
  exact IRasCR_wd.
Qed.

Lemma CRasIR_inv :  forall x, (CRasIR (- x) = [--] (CRasIR x))%CR.
Proof.
  intros. apply (injective IRasCR).
  rewrite IR_opp_as_CR.
  rewrite CRasIRasCR_id, CRasIRasCR_id.
  reflexivity.
Qed.

Lemma CR_leEq_as_IR :
∀ x y : CR , x ≤ y ↔ (CRasIR x [<=] CRasIR y).
Proof.
  intros x y.
  pose proof (IR_leEq_as_CR (CRasIR x) (CRasIR y)) as HH.
  rewrite CRasIRasCR_id in HH.
  rewrite CRasIRasCR_id in HH.
  symmetry. exact HH.
Qed.

Lemma CRasIR0 : CRasIR 0 = [0].
Proof.
  pose proof IR_Zero_as_CR as HH.
  apply CRasIR_wd in HH.
  rewrite IRasCRasIR_id in HH.
  symmetry. exact HH.
Qed.

Lemma CRasIR1 :  CRasIR CR1 [=] [1].
Proof using.
  apply (injective IRasCR).
  rewrite IR_One_as_CR.
  rewrite CRasIRasCR_id.
  reflexivity.
Qed.

Hint Rewrite CRasIR1 : CRtoIR.

(** Unlike CRpi_pos, this is transparent, so that we can compute pi inverse*)
Lemma CRpi_posT : (0 < CRpi)%CR.
Proof using.
  unfold CRltT.
  apply CR_epsilon_sign_dec_pos.
  exists (QposMake 1 1).
  vm_compute.
  reflexivity.
Defined.

Definition CRPiInv : CR := CRinvT CRpi (inr CRpi_posT).



Lemma CR_plus_asIR :
∀ x y : CR , CRasIR (x+y) = (CRasIR x [+] CRasIR y).
Proof.
  intros x y.
  pose proof (IR_plus_as_CR (CRasIR x) (CRasIR y)) as HH.
  rewrite CRasIRasCR_id in HH.
  rewrite CRasIRasCR_id in HH.
  apply CRasIR_wd in HH.
  rewrite <- HH.
  rewrite IRasCRasIR_id.
  reflexivity.
Qed.

Lemma CR_mult_asIR :
∀ x y : CR , CRasIR (x*y) = (CRasIR x [*] CRasIR y).
Proof.
  intros x y.
  pose proof (IR_mult_as_CR (CRasIR x) (CRasIR y)) as HH.
  rewrite CRasIRasCR_id in HH.
  rewrite CRasIRasCR_id in HH.
  apply CRasIR_wd in HH.
  rewrite <- HH.
  rewrite IRasCRasIR_id.
  reflexivity.
Qed.

Require Import  MathClasses.interfaces.additional_operations.
Lemma CRpower_N_asIR:
  ∀ (n: N) (x : CR), 
    CRasIR (x ^ n) = (((CRasIR x) [^] (N.to_nat n))%CR) .
Proof.
  intros ? ?.
  apply (injective IRasCR).
  rewrite CRpower_N_correct.
  rewrite CRasIRasCR_id.
  rewrite CRasIRasCR_id.
  reflexivity.
Qed.

Lemma CRasIRInj : ∀ q,
  CRasIR (inject_Q_CR q) = inj_Q IR q.
Proof.
  intros.
  apply (injective IRasCR).
  rewrite CRasIRasCR_id.
  autorewrite with IRtoCR.
  reflexivity.
Qed.
Hint Rewrite CRasIRInj : CRtoIR.


Hint Rewrite CRasIR0 CRasIR_inv CR_mult_asIR 
  CR_plus_asIR CRpower_N_asIR: CRtoIR .

Require Export CoRN.reals.R_morphism.

Lemma IRasCR_preserves_less : forall x y, (x[<]y -> IRasCR x < IRasCR y)%CR.
Proof.
 intros x y H.
  pose proof (iso_map_rht _ _ CRIR_iso).
  simpl. 
  apply (map_pres_less _ _  (iso_map_rht _ _ CRIR_iso)) in H.
  simpl in H.
  exact H.
Qed.

Lemma  CRltT_wdl : ∀ x1 x2 y : CR,
       x1 = x2  → (x1 < y)%CR → (x2 < y)%CR.
Proof.
  intros ? ? ? Heq.
  apply CRltT_wd; auto.
  reflexivity.
Qed.

Lemma  CRltT_wdr : ∀ x1 x2 y : CR,
       x1 = x2  → (y < x1)%CR → (y < x2)%CR.
Proof.
  intros ? ? ? Heq.
  apply CRltT_wd; auto.
  reflexivity.
Qed.


Lemma CREquiv_st_eq: forall a b : CR,
  st_eq (r:=CR) a  b <-> a = b.
Proof.
  reflexivity.
Qed.

Lemma CRApart_wdl :forall a b c:CR, 
  a = b -> a ≶ c -> b ≶ c.
Proof.
  intros ? ? ? Heq.
  apply strong_setoids.apart_proper; auto.
Qed.

Lemma CRsqr_nonneg : forall r, 0 ≤ r ^ 2.
Proof.
  intros r.
  apply CR_leEq_as_IR.
  autorewrite with CRtoIR.
  apply sqr_nonneg.
Qed.
  
Lemma  OnePlusSqrPos : forall r:CR, 0 < (1 + r ^ 2).
Proof.
  intros.
  apply semirings.pos_plus_le_lt_compat_l; auto;[| apply CRsqr_nonneg; fail].
  (* simpl. In Coq 8.5, simpl will unfold CR and confuse typeclass search*)
  apply positive_semiring_elements.Pos_1_obligation_1.
Qed.

Lemma  OnePlusSqrAp : forall r:CR, (1 + r ^ 2) ≶ 0.
Proof.
  intros. symmetry.
  apply orders.lt_iff_le_apart.
  apply OnePlusSqrPos.
Qed.

Ltac prepareForCRRing := 
  unfold zero, one, CR1, stdlib_rationals.Q_0, mult, cast,
  plus, CRplus,
  canonical_names.negate;
  try apply (proj1 (CREquiv_st_eq _ _)).


Ltac CRRing :=
    prepareForCRRing; ring.

Require Import Coq.QArith.Qfield.
Require Import Coq.QArith.Qring.
Require Import Psatz.

Lemma eq_implies_Qeq: forall a b : Q,
  eq a b -> Qeq a b.
Proof.
  intros ? ?  H. rewrite H.
  reflexivity.
Qed.
(** A and B can be different, e.g. rational_sqrt *)
Require Export CanonicalNotations.
Instance CRsqrt_SqrtFun_instance : SqrtFun CR CR := CRsqrt.
Instance rational_sqrt_SqrtFun_instance : SqrtFun Q CR 
    := rational_sqrt.
Instance : NormSpace CR CR := CRabs.


Ltac QRing_simplify :=
    repeat match goal with
    | [|- context [rational_sqrt ?q]] =>
          let qq := fresh "qq" in
          let Heqq := fresh "Heqq" in
           remember q as qq eqn:Heqq;
           apply eq_implies_Qeq in Heqq;
           ring_simplify in Heqq;
           rewrite Heqq;
           try (clear Heqq qq)
    | [|- context [@sqrtFun Q _ _ ?q]] =>
          let qq := fresh "qq" in
          let Heqq := fresh "Heqq" in
           remember q as qq eqn:Heqq;
           apply eq_implies_Qeq in Heqq;
           ring_simplify in Heqq;
           rewrite Heqq;
           try (clear Heqq qq)
    end.
  
Require Export CoRN.reals.fast.CRArith.

Lemma sr_mult_associative `{SemiRing R} (x y z : R) : x * (y * z) = x * y * z.
Proof. apply sg_ass, _. Qed.

Open Scope Q_scope.

Lemma inject_Q_CR_one  : (inject_Q_CR (1#1) [=] 1)%CR.
ring.
Qed.

Lemma inject_Q_CR_two  : (inject_Q_CR (2#1) = 2)%CR.
  rewrite <- inject_Q_CR_one.
  destruct CR_Q_ring_morphism.
  idtac. unfold plus, CRplus. rewrite <- morph_add; eauto.
Qed.

Lemma multNegShiftOut : forall a s : CR ,
(a * - s)%CR = (- (a * s))%CR.
Proof.
  intros. 
  CRRing.
Qed.

Lemma rational_sqrt_correct2: ∀ (a : Q) (H : [0] [<=] inj_Q IR a),
     CRasIR (rational_sqrt a) =  (sqrt (inj_Q IR a) H).
Proof using.
  intros ? ?.
  apply (injective IRasCR).
  rewrite CRasIRasCR_id.
  apply rational_sqrt_correct.
Qed.

Close Scope Q_scope.

Definition QCRM := CR_Q_ring_morphism.

Open Scope Q_scope.

Lemma CRPiBy2Correct :
  (CRpi * ' (1 # 2))%CR = IRasCR (Pi.Pi [/]TwoNZ).
Proof.
  apply (right_cancellation mult 2).
  match goal with 
  [ |- ?l = _] => remember l as ll
  end.
  rewrite <- IR_One_as_CR.
  unfold plus. unfold CRplus.
  rewrite <- IR_plus_as_CR.
  rewrite <- IR_mult_as_CR.
  subst.
  apply (injective CRasIR).
  rewrite IRasCRasIR_id.
  rewrite one_plus_one.
  rewrite div_1.
  apply (injective IRasCR).
  rewrite CRasIRasCR_id.
  rewrite CRpi_correct.
  fold (mult).
  rewrite <- sr_mult_associative.
  match goal with 
  [ |- ?l = _] => remember l as ll
  end.
  assert (CRpi [=] CRpi * 1)%CR as Hr by ring.
  rewrite Hr.
  subst ll.
  fold (mult).
  simpl. apply sg_op_proper;[reflexivity|].
  rewrite <- inject_Q_CR_two.
  rewrite <- (morph_mul QCRM).
  apply (morph_eq QCRM).
  reflexivity.
Qed.

Lemma  cos_cos_slow : forall x, cos x = cos_slow x.
Proof.
  intros x.
  unfold cos.
  generalize (Qround.Qceiling (approximate (x * CRinv_pos (6 # 1) (scale 2 CRpi))
   (1 # 2)%Qpos - (1 # 2)))%CR.
  intros z.
  rewrite -> compress_correct.
  rewrite <- (CRasIRasCR_id x).
  rewrite <- CRpi_correct, <- CRmult_scale, <- IR_inj_Q_as_CR, <- IR_mult_as_CR,
   <- IR_minus_as_CR, <- cos_slow_correct, <- cos_slow_correct.
  remember (CRasIR x) as y.
  clear dependent x. rename y into x.
  apply IRasCR_wd.
  rewrite -> inj_Q_mult.
  change (2:Q) with (Two:Q).
  rewrite -> inj_Q_nring.
  symmetry.
  rstepr (Cos (x[+]([--](inj_Q IR z))[*](Two[*]Pi))).
  setoid_replace (inj_Q IR z) with (zring z:IR).
  rewrite <- zring_inv.
  symmetry; apply Cos_periodic_Z.
  rewrite <- inj_Q_zring.
  apply inj_Q_wd.
  symmetry; apply zring_Q.
Qed.

Lemma cos_correct : forall x,
  (IRasCR (Cos x) == cos (IRasCR x))%CR.
Proof.
  intros x.
  rewrite cos_cos_slow.
  apply cos_slow_correct.
Qed.

Instance Setoid_Morphism_cos : Setoid_Morphism cos.
Proof.
  constructor; try apply st_isSetoid.
  intros a b Heq.
  rewrite cos_cos_slow, cos_cos_slow.
  rewrite Heq.
  reflexivity.
Qed.


Lemma cos_correct_CR : ∀ θ,
  CRasIR (cos θ) = (PowerSeries.Cos (CRasIR θ)).
Proof.
  intros θ. apply (injective IRasCR). rewrite cos_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.

Lemma  sin_sin_slow : forall x, sin x = sin_slow x.
Proof.
  intros x.
  unfold sin.
  generalize (Qround.Qceiling (approximate (x * CRinv_pos (6 # 1) (scale 2 CRpi))
   (1 # 2)%Qpos - (1 # 2)))%CR.
  intros z.
  rewrite -> compress_correct.
  rewrite <- (CRasIRasCR_id x).
  rewrite <- CRpi_correct, <- CRmult_scale, <- IR_inj_Q_as_CR, <- IR_mult_as_CR,
   <- IR_minus_as_CR, <- sin_slow_correct, <- sin_slow_correct.
  remember (CRasIR x) as y.
  clear dependent x. rename y into x.
  apply IRasCR_wd.
  rewrite -> inj_Q_mult.
  change (2:Q) with (Two:Q).
  rewrite -> inj_Q_nring.
  symmetry.
  rstepr (Sin (x[+]([--](inj_Q IR z))[*](Two[*]Pi))).
  setoid_replace (inj_Q IR z) with (zring z:IR).
  rewrite <- zring_inv.
  symmetry; apply Sin_periodic_Z.
  rewrite <- inj_Q_zring.
  apply inj_Q_wd.
  symmetry; apply zring_Q.
Qed.

Lemma sin_correct : forall x,
  (IRasCR (Sin x) == sin (IRasCR x))%CR.
Proof.
  intros x.
  rewrite sin_sin_slow.
  apply sin_slow_correct.
Qed.


Instance Setoid_Morphism_sin : Setoid_Morphism sin.
Proof.
  constructor; try apply st_isSetoid.
  intros a b Heq.
  rewrite sin_sin_slow, sin_sin_slow.
  rewrite Heq.
  reflexivity.
Qed.

Lemma sin_correct_CR : ∀ θ,
  CRasIR (sin θ) = (PowerSeries.Sin (CRasIR θ)).
Proof.
  intros θ. apply (injective IRasCR). rewrite sin_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.
Hint Rewrite sin_correct_CR cos_correct_CR : CRtoIR.

Lemma CR_Cos_HalfPi : (cos (CRpi * ' (1 # 2)) = 0 )%CR.
Proof.
  pose proof (Pi.Cos_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <- Hc.
  apply sm_proper.
  apply CRPiBy2Correct.
Qed.

Lemma CRCos_inv : forall x, (cos (-x) = cos x )%CR.
Proof.
  intros. apply (injective CRasIR).
  rewrite cos_correct_CR, cos_correct_CR.
  rewrite <- SinCos.Cos_inv.
  apply SinCos.Cos_wd.
  rewrite <-  CRasIR_inv.
  apply CRasIR_wd.
  ring.
Qed.


Lemma CR_Cos_Neg_HalfPi : (cos (CRpi * ' (-1 # 2)) = 0 )%CR.
Proof.
  rewrite <- CRCos_inv.
  rewrite <- CR_Cos_HalfPi.
  apply sm_proper.
  assert  (((-1#2)) = Qopp (1#2)) as Heq by reflexivity.
  rewrite Heq. clear Heq.
  rewrite (morph_opp QCRM).
  generalize (inject_Q_CR(1 # 2)).
  intros.  CRRing. 
Qed.


Lemma CR_Sin_HalfPi : (sin (CRpi * ' (1 # 2)) = 1 )%CR.
Proof.
  pose proof (Pi.Sin_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <- Hc.
  apply sm_proper.
  apply CRPiBy2Correct.
Qed.

Lemma CRSin_inv : forall x, (sin (-x) = - sin x )%CR.
Proof.
  intros. apply (injective CRasIR).
  rewrite sin_correct_CR.
  rewrite  CRasIR_inv, CRasIR_inv.
  rewrite SinCos.Sin_inv.
  rewrite sin_correct_CR.
  apply csf_fun_wd.
  reflexivity.
Qed.

(*Lemma CREqOpp: forall a b : CR,
  -a = -b -> a = b.
Proof.
  intros ? ? Heq. 
  rewrite <- CREquiv_st_eq.
  rewrite <- CREquiv_st_eq.
  prepareForCRRing.
  intros. intros.  ring.

  unfold equiv. fold (st_eq (r:=CR)).
  
  intro.   CRRing.
  apply  (  Ropp_ext CR_ring_eq_ext) in Heq.
*)



Lemma CR_Sin_Neg_HalfPi : (sin (CRpi * ' (-1 # 2)) = - 1 )%CR.
Proof.
  rewrite <- CR_Sin_HalfPi.
  rewrite <- CRSin_inv.
  apply sm_proper.
  assert  (((-1#2)) = Qopp (1#2)) as Heq by reflexivity.
  rewrite Heq. clear Heq.
  rewrite (morph_opp QCRM).
  apply multNegShiftOut.
Qed.
Instance CRpi_RealNumberPi_instance : RealNumberPi CR := CRpi.

Instance Q_Half_instance : HalfNum Q := (1#2).
Instance CR_Half_instance : HalfNum CR := (inject_Q_CR (1#2)).

Close Scope Q_scope.

Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Require Import IRMisc.LegacyIRRing.


Lemma Cos_minus_Pi : ∀ θ : IR, Cos (θ[-]Pi)[=][--](Cos θ).
Proof.
  intros.
  rewrite <-Cos_periodic.
  rewrite <- Cos_plus_Pi.
  apply Cos_wd.
  rewrite <-one_plus_one.
  unfold cg_minus.
  ring.
Qed.

Lemma Sin_minus_Pi : ∀ θ : IR, Sin (θ[-]Pi)[=][--](Sin θ).
Proof.
  intros.
  rewrite <-Sin_periodic.
  rewrite <- Sin_plus_Pi.
  apply Sin_wd.
  rewrite <-one_plus_one.
  unfold cg_minus.
  ring.
Qed.

Lemma CRCos_plus_Pi: ∀θ , cos (θ + π) = - (cos θ).
  intros θ.
  pose proof (Pi.Cos_plus_Pi (CRasIR θ)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  exact Hc.
Qed.

Lemma CRSin_plus_Pi: ∀ θ : CR, sin (θ + π) = (- sin θ).
  intros x.
  pose proof (Pi.Sin_plus_Pi (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  exact Hc.
Qed.

Lemma CRCos_minus_Pi: ∀θ , cos (θ - π) = - (cos θ).
  intros θ.
  pose proof (Cos_minus_Pi (CRasIR θ)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  exact Hc.
Qed.

Lemma CRSin_minus_Pi: ∀ θ : CR, sin (θ - π) = (- sin θ).
  intros x.
  pose proof (Sin_minus_Pi (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  exact Hc.
Qed.

Definition QSign `{Negate A} (q : Q) (a:A) : A :=
  if (decide (q < 0)) then (-a) else (a).

Lemma CRCos_PlusMinus_Pi: ∀θ q, cos (θ + (QSign q π)) = - (cos θ).
  intros θ q. unfold QSign.
  destruct (decide (q < 0));[apply CRCos_minus_Pi|apply CRCos_plus_Pi].
Qed.

Lemma CRSin_PlusMinus_Pi: ∀θ q, sin (θ + (QSign q π)) = - (sin θ).
  intros θ q. unfold QSign.
  destruct (decide (q < 0));[apply CRSin_minus_Pi|apply CRSin_plus_Pi].
Qed.


Lemma arctan_correct_CR : ∀ θ,
  CRasIR (arctan θ) = (ArcTan (CRasIR θ)).
Proof.
  intros θ. apply (injective IRasCR). rewrite arctan_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.


(** One could also divide [π] by 2. However,
    division seems to be annoyingly difficult to deal with.
    For example, rewrite fails with an error about
    inability to handle dependence. Also, one has
    to carry around proofs of positivity *)

Lemma CRPiBy2Correct1 :
  ½ * π = IRasCR (Pi.Pi [/]TwoNZ).
Proof.
  rewrite <- CRPiBy2Correct.
  rewrite rings.mult_comm.
  reflexivity.
Qed.

Lemma MinusCRPiBy2Correct :
  - (½ * π) = IRasCR ([--] (Pi.Pi [/]TwoNZ)).
Proof.
  autorewrite with IRtoCR.
  rewrite <- CRPiBy2Correct.
  rewrite rings.mult_comm.
  reflexivity.
Qed.


Lemma CRpower_N_2 : forall y,
    CRpower_N y (N.of_nat 2) = y * y.
Proof.
  intros y.
  assert ((N.of_nat 2) = (1+(1+0))) as Hs by reflexivity.
  rewrite Hs.
  destruct NatPowSpec_instance_0.
  rewrite nat_pow_S.
  rewrite nat_pow_S.
  rewrite nat_pow_0.
  simpl. prepareForCRRing.
  unfold CR1. CRRing.
Qed.


Lemma CRsqrt_ofsqr_nonneg :  
  ∀ y: CR, 0 ≤ y -> CRsqrt (y * y) = y.
Proof.
  intros ? Hle.
  apply CR_leEq_as_IR in Hle.
  autorewrite with CRtoIR in Hle.
  eapply NRootIR.sqrt_to_nonneg in Hle.
  apply IRasCR_wd in Hle.
  rewrite CRsqrt_correct in Hle.
  rewrite CRasIRasCR_id in Hle.
  remember (y * y) as yy.
  rewrite <- Hle. clear Hle.
  apply uc_wd_Proper.
  autorewrite with IRtoCR.
  rewrite CRasIRasCR_id.
  subst yy.
  rewrite <- CRpower_N_2.
  reflexivity.
  Grab Existential Variables.
  apply sqr_nonneg.
Qed.

Lemma CRsqrt_ofsqr_nonpos :  
  ∀ y: CR, y ≤ 0 -> CRsqrt (y * y) = -y.
Proof.
  intros ? Hle.
  apply CR_leEq_as_IR in Hle.
  autorewrite with CRtoIR in Hle.
  eapply NRootIR.sqrt_to_nonpos in Hle.
  apply IRasCR_wd in Hle.
  rewrite CRsqrt_correct in Hle.
  rewrite  IR_opp_as_CR in Hle.
  rewrite CRasIRasCR_id in Hle.
  remember (y * y) as yy.
  rewrite <- Hle. clear Hle.
  apply uc_wd_Proper.
  autorewrite with IRtoCR.
  rewrite CRasIRasCR_id.
  subst yy.
  rewrite <- CRpower_N_2.
  reflexivity.
  Grab Existential Variables.
  apply sqr_nonneg.
Qed.

Lemma CRrational_sqrt_ofsqr_nonneg:  
  ∀ y, 0 ≤ y -> rational_sqrt (y * y) = 'y.
Proof.
  intros ? Hle.
  rewrite <- CRsqrt_Qsqrt.
  rewrite (morph_mul QCRM).
  apply CRsqrt_ofsqr_nonneg.
  apply CRle_Qle.
  trivial.
Qed.

Lemma CRrational_sqrt_ofsqr_nonpos:  
  ∀ y, y ≤ 0 -> rational_sqrt (y * y) = '(-y).
Proof.
  intros ? Hle.
  rewrite <- CRsqrt_Qsqrt.
  rewrite (morph_mul QCRM).
  apply CRsqrt_ofsqr_nonpos.
  apply CRle_Qle.
  trivial.
Qed.

Ltac prepareForLra :=
  unfold le, stdlib_rationals.Q_le,
         lt, stdlib_rationals.Q_lt.

Lemma CRrational_sqrt_ofsqr:
  ∀ y, rational_sqrt (y * y) = 
      '(if (decide (y < 0)) then -y else y).
Proof.
  intros y.
  destruct (decide (y < 0)) as [Hd | Hd];
    [apply CRrational_sqrt_ofsqr_nonpos|
     apply CRrational_sqrt_ofsqr_nonneg];
         revert Hd; prepareForLra; intro; lra.
Qed.

Hint Rewrite CR_Cos_Neg_HalfPi CR_Cos_HalfPi
             CR_Sin_Neg_HalfPi CR_Sin_HalfPi 
             CRCos_plus_Pi CRSin_plus_Pi: CRSimpl.

Definition projCR (cp : CR ₀) : CR.
  destruct cp as [x ap]. exact x.
Defined.

Require Export IRMisc.IRTrig.


(*Instance castCRIR : Cast CR IR := CRasIR. *)

Lemma CRdivideToMul: 
  forall na da dap nb db dbp,
  na*db = nb*da -> na // (da ↾ dap) = nb // (db ↾ dbp).
Proof.
  simpl. intros ? ? ? ? ? ? Heq.
  apply  fields.equal_quotients.
  simpl.
  exact Heq.
Qed.

Definition mkCr0 (a : CR) (ap : (a >< 0)%CR)  : CR ₀.
  exists a. simpl. apply CR_apart_apartT in ap.
  exact ap.
Defined.

Lemma  CRinv_CRinvT : forall
  (a : CR) (ap : (a >< 0)%CR),
  CRinvT a ap = CRinv (mkCr0 a ap).
Proof.
  intros. unfold CRinv.
  simpl. apply CRinvT_wd.
  reflexivity.
Qed.



Lemma CRdivideToMulCRInvT: 
  forall na da dap nb db dbp,
  na*db = nb*da -> na * (CRinvT da  dap) = nb * (CRinvT db  dbp).
Proof.
  intros ? ? ? ? ? ? Heq.
  rewrite CRinv_CRinvT, CRinv_CRinvT.
  apply    fields.equal_quotients.
  simpl.
  exact Heq.
Qed.

Lemma CRdivideToMulCRInv: 
  forall na da dap nb db dbp,
  na*db = nb*da
  -> na // da ↾ dap = nb // db ↾ dbp.
Proof.
  intros ? ? ? ? ? ? Heq.
  apply    fields.equal_quotients.
  simpl.
  exact Heq.
Qed.

Lemma CRdivideToMulCRInv2: 
  forall na da dap nb db dbp,
  na*db = nb*da
  -> na * (CRinv (da ↾ dap)) = nb * (CRinv (db ↾ dbp)).
Proof.
  intros ? ? ? ? ? ? Heq.
  apply    fields.equal_quotients.
  simpl.
  exact Heq.
Qed.

Lemma sqr_o_cos_o_arctan : forall r p,
    (cos (arctan r)) ^2 = (1 //((1 + r^2) ↾ p)).
Proof.
  intros x p. simpl in p.
  pose proof (CosOfArcTan2 (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  rewrite Hc. clear Hc.
  rewrite IR_div_as_CR_1.
  simpl. unfold cf_div. unfold f_rcpcl, f_rcpcl'.
  simpl. unfold recip,CRinv. 
  apply CRdivideToMulCRInvT.
  autorewrite with IRtoCR.
  rewrite CRasIRasCR_id.
  simpl. rewrite CRpower_N_2.
  prepareForCRRing.
  simpl. CRRing.
Qed.

Lemma sqr_o_sin_o_arctan : forall r p,
    (sin (arctan r)) ^2 = (r^2 //((1 + r^2) ↾ p)).
Proof.
  intros x p. simpl in p.
  pose proof (SinOfArcTan2 (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  rewrite Hc. clear Hc.
  rewrite IR_div_as_CR_1.
  simpl. unfold cf_div. unfold f_rcpcl, f_rcpcl'.
  simpl. unfold recip,CRinv. 
  apply CRdivideToMulCRInvT.
  autorewrite with IRtoCR.
  rewrite CRasIRasCR_id.
  simpl. rewrite CRpower_N_2.
  prepareForCRRing.
  simpl.  CRRing.
Qed.


Definition mkCr0' (a : CR) (ap : (a ≶ 0)%CR)  : CR ₀ :=
   (a ↾ ap).

Lemma sqr_o_cos_o_arctan2 : forall r,
    (cos (arctan r)) ^2 = (1 //(mkCr0' (1 + r^2) (OnePlusSqrAp _))).
Proof.
  intros. apply sqr_o_cos_o_arctan.
Qed.

Lemma sqr_o_cos_o_Qarctan : forall (r:Q),
    (cos (rational_arctan r)) ^2 = ' (1 /(1 + r^2)).
Proof.
  intros. rewrite <- arctan_Qarctan.
  rewrite sqr_o_cos_o_arctan2.
  idtac. unfold recip.
  rewrite <- CRmult_Qmult.
  rewrite <- CRinv_Qinv.
  rewrite CRinv_CRinvT.
  apply CRdivideToMulCRInv2.
  rewrite CRpower_N_2. 
  unfold pow, stdlib_rationals.Q_Npow. simpl. 
  rewrite <- CRplus_Qplus.
  rewrite <- CRmult_Qmult.
  reflexivity.
  Grab Existential Variables.
  unfold pow, stdlib_rationals.Q_Npow. simpl.
  stepl (1 + (('r) ^2));
   [|rewrite <- CRplus_Qplus, <- CRmult_Qmult, 
          <- CRpower_N_2; reflexivity].
  apply CR_apart_apartT.
  apply OnePlusSqrAp.
Qed.


(** use autounfold with QMC instead *)
Ltac unfoldMC :=
  unfold pow, stdlib_rationals.Q_Npow, plus,
  one, zero, stdlib_rationals.Q_1, stdlib_rationals.Q_plus,
  stdlib_binary_naturals.N_plus,
  stdlib_binary_naturals.N_1,
  equiv, stdlib_rationals.Q_eq, mult,
  stdlib_rationals.Q_mult, dec_recip,
  stdlib_rationals.Q_recip,
  zero, stdlib_rationals.Q_0,
  le, stdlib_rationals.Q_le,
  lt, stdlib_rationals.Q_lt,
  canonical_names.negate, stdlib_rationals.Q_opp.

Hint Unfold pow stdlib_rationals.Q_Npow plus
  one zero stdlib_rationals.Q_1 stdlib_rationals.Q_plus
  stdlib_binary_naturals.N_plus
  stdlib_binary_naturals.N_1
  equiv stdlib_rationals.Q_eq mult
  stdlib_rationals.Q_mult dec_recip
  stdlib_rationals.Q_recip
  zero stdlib_rationals.Q_0
  le stdlib_rationals.Q_le
  lt stdlib_rationals.Q_lt
  canonical_names.negate stdlib_rationals.Q_opp  : QMC.


Lemma QSumOfSqr0Implies : ∀ x y,
  (x * x + y * y == 0)%Q
   -> (x==0)%Q.
Proof.
  intros ? ? Heq.
  pose proof (Qpower.Qsqr_nonneg x) as Hx.
  pose proof (Qpower.Qsqr_nonneg y) as Hy.
  simpl in Hx, Hy.
  assert (x * x ==0)%Q as Hx0 by lra.
  clear Hx Hy.
  apply Qmult_integral in Hx0.
  tauto.
Qed.



Require  Import MathClasses.orders.rings.
Require  Import MathClasses.theory.rings.
Require  Import MCMisc.fields.

  
(* useful for conversion from 
    cartesian to polar co-ordinates*)
Lemma sqr_o_cos_o_Qarctan_o_div : forall (x y :Q),
    x ≠ 0
    -> (cos (rational_arctan (y/x))) ^2 = ' (x^2 /(x^2 + y^2)).
Proof.
  intros ? ? H. rewrite sqr_o_cos_o_Qarctan.
  apply inject_Q_CR_wd.
  unfoldMC. simpl.
  field. split; auto.
  intros Hc. apply H.
  apply QSumOfSqr0Implies in Hc.
  assumption.
Qed.

Lemma sqr_o_sin_o_arctan2 : forall r,
    (sin (arctan r)) ^2 = (r^2 //(mkCr0' (1 + r^2) (OnePlusSqrAp _))).
Proof.
  intros. apply sqr_o_sin_o_arctan.
Qed.

Lemma sqr_o_sin_o_Qarctan : forall (r:Q),
    (sin (rational_arctan r)) ^2 = ' (r^2 /(1 + r^2)).
Proof.
  intros. rewrite <- arctan_Qarctan.
  rewrite sqr_o_sin_o_arctan2.
  idtac. unfold recip.
  rewrite <- CRmult_Qmult.
  rewrite <- CRinv_Qinv.
  rewrite CRinv_CRinvT.
  apply CRdivideToMulCRInv2.
  rewrite CRpower_N_2. 
  unfold pow, stdlib_rationals.Q_Npow. simpl. 
  rewrite <- CRplus_Qplus.
  rewrite <- CRmult_Qmult.
  reflexivity.
  Grab Existential Variables.
  unfold pow, stdlib_rationals.Q_Npow. simpl.
  stepl (1 + (('r) ^2));
   [|rewrite <- CRplus_Qplus, <- CRmult_Qmult, 
          <- CRpower_N_2; reflexivity].
  apply CR_apart_apartT.
  apply OnePlusSqrAp.
Qed.

(* useful for conversion from 
    cartesian to polar co-ordinates*)
Lemma sqr_o_sin_o_Qarctan_o_div : forall (x y :Q),
    x ≠ 0
    -> (sin (rational_arctan (y/x))) ^2 = ' (y^2 /(x^2 + y^2)).
Proof.
  intros ? ? H. rewrite sqr_o_sin_o_Qarctan.
  apply inject_Q_CR_wd.
  unfoldMC. simpl.
  field. split; auto.
  intros Hc. apply H.
  apply QSumOfSqr0Implies in Hc.
  assumption.
Qed.

Lemma CRCos_nonneg:
  ∀ θ, -(½ * π) ≤ θ ≤ ½ * π
        → 0 ≤ cos θ.
Proof.
  intros ? Hp. destruct Hp as [Hpt Htp].
  pose proof (TrigMon.Cos_nonneg (CRasIR θ)) as Hir.
  apply CR_leEq_as_IR.
  autorewrite with CRtoIR.
  rewrite CRPiBy2Correct1 in Htp.
  apply CR_leEq_as_IR in Htp.
  rewrite IRasCRasIR_id in Htp.
  apply Hir; trivial;[].
  clear Htp Hir.
  apply IR_leEq_as_CR.
  rewrite CRasIRasCR_id.
  rewrite  <- MinusCRPiBy2Correct.
  exact Hpt.
Qed.



Lemma CRarctan_range:
 ∀ r : CR, (-(½ * π) < arctan r < ½ * π).
Proof.
  intros r.
  pose proof (InvTrigonom.ArcTan_range (CRasIR r)) as Hir.
  destruct Hir as [Hirl Hirr].
  eapply less_wdl in Hirr;
    [|symmetry; apply arctan_correct_CR].
  eapply less_wdr in Hirl;
    [| symmetry; apply arctan_correct_CR].
  apply IRasCR_preserves_less in Hirr.
  apply IRasCR_preserves_less in Hirl.
  eapply CRltT_wdr in Hirl;
    [| apply CRasIRasCR_id].
  eapply CRltT_wdl in Hirr;
    [| apply CRasIRasCR_id].
  eapply CRltT_wdr in Hirr;
    [| symmetry; apply CRPiBy2Correct1].
  split; unfold lt; apply CR_lt_ltT; auto;[].
  clear Hirr.
  eapply CRltT_wdl in Hirl;
    [| symmetry; apply MinusCRPiBy2Correct].
  assumption.
Qed.

Lemma CRweakenLt :
  ∀ a t: CR, a < t -> a ≤ t.
Proof.
  intros ? ? Hlt.
  apply orders.full_pseudo_srorder_le_iff_not_lt_flip.
  intros Hc.
  pose proof (conj Hc Hlt) as Hr.
  apply orders.pseudo_order_antisym in Hr.
  assumption.
Qed.

Hint Resolve CRweakenLt : CRBasics.


Lemma CRweakenRange :
  ∀ a t b: CR,
    a < t < b
    -> a ≤ t ≤ b.
Proof.
  intros ? ? ? Hr.
  destruct Hr.
  split; eauto using CRweakenLt.
Qed.



Lemma CRMult00Eq0 : (0 * 0 = 0)%CR.
Proof.
  CRRing.
Qed.


Lemma CRsqrt0 : (√0 = 0)%CR.
Proof.
  rewrite <- CRMult00Eq0.
  apply CRsqrt_ofsqr_nonpos.
  reflexivity.
Qed.

Lemma CRsqrt_nonneg: 
    ∀ (x : CR),  0 ≤ x -> 0 ≤ √x.
Proof.
  intros x Hle.
  apply CR_leEq_as_IR in Hle.
  autorewrite with CRtoIR in Hle.
  pose proof (sqrt_nonneg (CRasIR x) Hle) as Hir.
  apply IR_leEq_as_CR in Hir.
  autorewrite with IRtoCR in Hir.
  rewrite CRasIRasCR_id in Hir.
  exact Hir.
Qed.

Lemma CRrational_sqrt_nonneg: 
    ∀ (x : Q), 0 ≤ √x.
Proof.
  intros x.
  destruct (decide (0 < x)) as [Hdec | Hdec].
- rewrite <- CRsqrt_Qsqrt.
  apply CRsqrt_nonneg.
  apply CRweakenLt.
  apply CR_lt_ltT.
  apply  CRlt_Qlt. assumption.
- apply orders.full_pseudo_srorder_le_iff_not_lt_flip in Hdec.
  rewrite rational_sqrt_nonpos;
    [reflexivity|assumption].
Qed.

Ltac ApplyEq F H :=
let Hf := fresh H in
match type of H with
equiv ?a ?b => assert (equiv (F a)  (F b)) as Hf by (rewrite H; reflexivity);
    clear H; rename Hf into H
end.

Tactic Notation  "applyEq" constr(F) "in" ident(H) :=
ApplyEq F H.


(* using [mult_eq_zero] will result in a lemma
    where [a+b] needs to be strictly positive *)
Lemma EqIfSqrEqNonNeg :forall (a b : CR),
  0 ≤ a ->   0 ≤ b   ->   a * a = b * b  -> a = b.
Proof.
  intros ? ? ? ? Hsq.
  applyEq CRsqrt in Hsq.
  rewrite CRsqrt_ofsqr_nonneg in Hsq by assumption.
  rewrite CRsqrt_ofsqr_nonneg in Hsq by assumption.
  assumption.
Qed.

Lemma EqIfSqrEqNonPos :forall (a b : CR),
  a ≤ 0 ->   b ≤ 0   ->   a * a = b * b  -> a = b.
Proof.
  intros ? ? ? ? Hsq.
  applyEq CRsqrt in Hsq.
  rewrite CRsqrt_ofsqr_nonpos in Hsq by assumption.
  rewrite CRsqrt_ofsqr_nonpos in Hsq by assumption.
  apply (proj2 (CREquiv_st_eq _ _)) in Hsq.
  apply (injective CRopp) in Hsq.
  assumption.
Qed.


Lemma cos_o_arctan_nonneg: ∀ r : CR,  0 ≤ cos (arctan r).
Proof.
  intros ?.
  apply CRCos_nonneg.
  apply CRweakenRange.
  apply CRarctan_range.
Qed.

Lemma CRsqrt_resp_less :
∀ (x y : CR), 0 ≤ x  → 0 ≤ y   → x < y → √x < √y.
Proof.
  intros ? ?.
  pose proof (sqrt_resp_less (CRasIR x) (CRasIR y)) as Hir.
  intros Hx Hy Hxy.
  apply CR_leEq_as_IR in Hx.
  apply CR_leEq_as_IR in Hy.
  autorewrite with CRtoIR in Hy, Hx.
  specialize (Hir Hx Hy).
Abort.
  
  
Lemma  SqrtOnePlusSqrPos : 
    ∀ r:CR, 0 < √(1 + r ^ 2).
Proof.
  intros.
Abort.


Lemma  SqrtOnePlusSqrAp : forall r:CR, 
    (CRsqrt (1 + r ^ 2)) ≶ 0.
Proof.
Abort.

Lemma cos_o_arctan : forall r,
    (√(1 + r^2)) * (cos (arctan r)) = 1.
Proof.
Abort.

Lemma CRsqrt_mult:
  ∀ (x y : CR),  0 ≤ x → 0 ≤ y → 
  CRsqrt(x*y) = (CRsqrt x) * (CRsqrt y).
Proof.
  intros x ? Hx Hy.
  apply CR_leEq_as_IR in Hx.
  apply CR_leEq_as_IR in Hy.
  autorewrite with CRtoIR in Hx.
  autorewrite with CRtoIR in Hy.
  pose proof (sqrt_mult (CRasIR x) (CRasIR y) Hx Hy 
        (mult_resp_nonneg _ _ _ Hx Hy)) as Hir.
  apply IRasCR_wd in Hir.
  autorewrite with IRtoCR in Hir.
  rewrite CRasIRasCR_id in Hir.
  rewrite CRasIRasCR_id in Hir.
  exact Hir.
Qed.


Lemma CRsqrt_sqr:
  ∀ (x : CR), 
  0 ≤ x
  -> (CRsqrt x)^2 = x.
Proof.
  intros x Hx.
  apply CR_leEq_as_IR in Hx.
  autorewrite with CRtoIR in Hx.
  pose proof (sqrt_sqr (CRasIR x) Hx) as Hir.
  apply IRasCR_wd in Hir.
  autorewrite with IRtoCR in Hir.
  rewrite CRasIRasCR_id in Hir.
  exact Hir.
Qed.

Lemma CRsqrt_sqr1:
  ∀ (x y : CR), (CRsqrt (x^2 + y^2)) ^ 2 = (x^2 + y^2).
Proof.
  intros.
  apply CRsqrt_sqr.
  apply semirings.nonneg_plus_compat; unfold PropHolds;
  apply CRsqr_nonneg.
Qed.

Hint Rewrite <- CRplus_Qplus CRmult_Qmult  : MoveInjQCRIn.


Lemma CRPowOfRational : ∀ (q:Q) (n:nat),
   (inject_Q_CR q) ^ n = '(q ^ n).
Proof.
  intros ? ?. idtac. unfold pow. 
  induction n;[reflexivity|].
  unfoldMC. simpl.
  autorewrite with MoveInjQCRIn.
  rewrite IHn.
  reflexivity.
Qed.

Ltac foldZeroMC :=
match goal with
  [|- context [N0]] =>   fold (stdlib_binary_naturals.N_0);
        fold (@zero N stdlib_binary_naturals.N_0)
end.

Ltac foldOneMC :=
match goal with
  [|- context [1%N]] =>   fold (stdlib_binary_naturals.N_1);
        fold (@one N stdlib_binary_naturals.N_1)
end.

Ltac foldPlusMC :=
match goal with
  [|- context [(?a+?b)%N]] =>   fold (stdlib_binary_naturals.N_plus a b);
        fold (@plus N stdlib_binary_naturals.N_plus a b)
end.

Lemma CRPowOfRationalN : ∀ (q:Q) (n:N),
   (inject_Q_CR q) ^ n = '(q ^ n).
Proof.
  intros ? ?. idtac.
  induction n using N.peano_ind;
    [foldZeroMC;rewrite nat_pow_0; reflexivity|].
  rewrite <- N.add_1_l. foldOneMC. 
  foldPlusMC. rewrite nat_pow_S. rewrite nat_pow_S.
  rewrite IHn.
  autorewrite with MoveInjQCRIn.
  reflexivity.
Qed.

Hint Rewrite <- CRPowOfRational CRPowOfRationalN  : MoveInjQCRIn.

Lemma CRsqrt_sqr1Q:
  ∀ (x y : Q), (rational_sqrt (x^2 + y^2)) ^ 2 = ' (x^2 + y^2).
Proof.
  intros.
  rewrite <- CRsqrt_Qsqrt. 
  rewrite  CRsqrt_sqr;[reflexivity|].
  apply CRle_Qle.
  pose proof (Qpower.Qsqr_nonneg x) as Hx.
  pose proof (Qpower.Qsqr_nonneg y) as Hy.
  lra.
Qed.


Lemma CRsqrt_sqr1Q1:
  ∀ (x y : Q), (rational_sqrt (x^2 + y^2)) * (rational_sqrt (x^2 + y^2)) 
      = ' (x^2 + y^2).
Proof.
  intros.
  rewrite <- CRpower_N_2. 
  simpl. apply CRsqrt_sqr1Q.
Qed.

Lemma sqrProdRW : forall c d : CR , d * c * (d * c) = (d*d)*(c*c).
Proof.
  intros c d. CRRing.
Qed.
Require Import  MathClasses.interfaces.additional_operations.
Hint Rewrite  CRplus_Qplus CRmult_Qmult CRopp_Qopp : MoveInjQCROut.

Lemma cos_o_arctan_east: ∀ (cy cx : Q), 
    (0 < cx)%Q
    → 'cx = √ (cx * cx + cy * cy)%Q * cos (rational_arctan (cy/cx)).
Proof.
  intros ? ? Hcx. assert (0 ≤ cx ) as Hle by (unfoldMC; lra).
  apply CRle_Qle in Hle.
  rewrite <- arctan_Qarctan. apply EqIfSqrEqNonNeg; trivial;
        [apply orders.nonneg_mult_compat; unfold PropHolds;
          eauto using CRrational_sqrt_nonneg, cos_o_arctan_nonneg; fail|].
  rewrite sqrProdRW.
  symmetry.
  rewrite rings.mult_comm.
  rewrite <- CRpower_N_2. 
  rewrite  arctan_Qarctan.
  unfold recip, dec_fields.recip_dec_field, dec_recip,
    stdlib_rationals.Q_recip, mult, stdlib_rationals.Q_mult.
    simpl. idtac. fold (Qdiv cy cx).
  assert ((cx ≠ 0 )) as Hneq by (unfoldMC; lra).
  rewrite sqr_o_cos_o_Qarctan_o_div;[|assumption].
  unfold sqrtFun, rational_sqrt_SqrtFun_instance.
  let rs := eval simpl in (CRsqrt_sqr1Q1 cx cy) in rewrite rs.
  autorewrite with MoveInjQCROut.
  apply inject_Q_CR_wd.
  unfoldMC. simpl. 
  field.
  intro Hc. apply Hneq.
  apply QSumOfSqr0Implies in Hc. assumption.
Qed.

Require Import MCMisc.rings.
Lemma sqr_o_cos_o_arctan_o_div : forall (x y :CR) p,
 (x^2 + y^2) * (cos (arctan (y//(x ↾ p)))) ^2 =  x^2.
Proof.
  intros ? ? H. rewrite sqr_o_cos_o_arctan2.
  symmetry.
  rewrite (@simple_associativity _ _ mult _ _).
  rewrite (@rings.mult_1_r _ _ _ _ _ _ _ _).
  symmetry.
  apply equal_quotientsl.
  Local Opaque CR.
  simpl.
  rewrite rings.plus_mult_distr_l.
  rewrite  rings.mult_1_r.
  apply sg_op_proper;[reflexivity|].
  do 3 rewrite nat_pow.nat_pow_2.
  remember (// x ↾ H) as xh.
  assert (x * x * (y * xh * (y * xh))
    = (y*y)*(x*xh)*(x*xh)) as Heq by (unfoldMC;ring).
  rewrite Heq. clear Heq.
  subst xh. rewrite fields.reciperse_alt.
  rewrite rings.mult_1_r.
  rewrite rings.mult_1_r.
  reflexivity.
Qed.

Lemma cos_o_Rarctan_east: ∀ (cy cx : CR) p, 
    (0 < cx)
    → cx = √ (cx * cx + cy * cy) * cos (arctan (cy//(cx ↾ p))).
Proof.
  intros ? ? ? Hcx. simpl in Hcx. simpl in p.
  pose proof (CRweakenLt _ _ Hcx) as Hle.
  apply EqIfSqrEqNonNeg; [assumption |   |].
  - apply orders.nonneg_mult_compat; unfold PropHolds;
      [| apply cos_o_arctan_nonneg].
    apply CRsqrt_nonneg.
    apply nonneg_plus_compat; simpl; apply square_nonneg.
  - rewrite <- (@nat_pow.nat_pow_2 CR _ _ _ _ _ _ _ _ _ _ _ _ _ _
      CRpower_N _ cy).
    rewrite <- (@nat_pow.nat_pow_2 CR _ _ _ _ _ _ _ _ _ _ _ _ _ _
      CRpower_N _ cx).
    rewrite (@simple_associativity  _ _ mult _ _).
    rewrite MultSqrMix.
    rewrite <- (@nat_pow.nat_pow_2 CR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRpower_N 
      _ _).
    rewrite <- (@nat_pow.nat_pow_2 CR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRpower_N 
      _ _).
    unfold sqrtFun, CRsqrt_SqrtFun_instance.
    rewrite CRsqrt_sqr1.
    symmetry.
    apply sqr_o_cos_o_arctan_o_div.
Qed.


Lemma cos_o_RQarctan_east:
  ∀ (cy: CR) (cx:Q),
    (0<cx)%Q
  -> 'cx = ((√ ('(cx * cx) + cy * cy)))
                   * cos ((arctan (cy *'(/cx)))).
Proof using.
  intros ? ? Hb.
  rewrite preserves_mult.
  pose proof Hb as Hbb.
  apply (@preserves_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cast Q CR) _ _) in Hb.
  rewrite <- CRinv_Qinv.
  rewrite CRinv_CRinvT.
  apply cos_o_Rarctan_east.
  exact Hb.
  Grab Existential Variables.
  apply CR_apart_apartT.
  symmetry.
  apply lt_apart.
  assumption.
Qed.

Lemma CRSin_nonneg:
  ∀ θ, 0 ≤ θ ≤  π   → 0 ≤ sin θ.
Proof.
  intros ? Hp. destruct Hp as [Hpt Htp].
  pose proof (Sin_nonneg (CRasIR θ)) as Hir.
  apply CR_leEq_as_IR.
  autorewrite with CRtoIR.
  apply Hir;
  apply IR_leEq_as_CR;
  rewrite CRasIRasCR_id;
  autorewrite with IRtoCR; assumption.
Qed.

Hint Rewrite <- CRasIR0 : CRtoIR.

Lemma CRArcTan_zero: arctan 0 = 0.
Proof.
  pose proof (ArcTan_zero) as HH.
  apply (injective CRasIR).
  rewrite arctan_correct_CR.
  match goal with
  | [|-?l = ?r] => remember l
  end.
  rewrite CRasIR0.
  rewrite <- HH.
  subst.
  apply ArcTan_wd.
  apply CRasIR0.
Qed.

Lemma CRArcTan_resp_leEq : ∀ x y, x ≤ y -> arctan x ≤ arctan y.
Proof.
  intros ? ? Hless.
  apply CR_leEq_as_IR in Hless.
  pose proof (ArcTan_resp_leEq (CRasIR x) (CRasIR y) Hless) as Hir.
  apply IR_leEq_as_CR in Hir.
  autorewrite with IRtoCR in Hir.
  rewrite CRasIRasCR_id in Hir.
  rewrite CRasIRasCR_id in Hir.
  assumption.
Qed.


(** a good example of proof by computation *)
Lemma  PiHalfLt :    (½ * π) < π.
Proof. 
  intros. unfold lt, CRlt. exists 1%nat.
  simpl. vm_compute. reflexivity.
Qed.


Lemma arctan_nonneg : ∀ r, 
  0 ≤ r -> 0 ≤ arctan r.
Proof.
  intros ? Hle.
  pose proof (CRArcTan_resp_leEq 0 r Hle) as Hxx.
  rewrite CRArcTan_zero in Hxx.
  assumption.
Qed.

Lemma arctan_nonpos : ∀ r, 
  r ≤ 0 -> arctan r ≤ 0.
Proof.
  intros ? Hle.
  pose proof (CRArcTan_resp_leEq _ _ Hle) as Hxx.
  rewrite CRArcTan_zero in Hxx.
  assumption.
Qed.

Lemma rational_arctan_nonneg : ∀ r, 
  0 ≤ r -> 0 ≤ rational_arctan r.
Proof.
  intros ? Hle.
  rewrite <- arctan_Qarctan.
  apply arctan_nonneg.
  apply CRle_Qle.
  assumption.
Qed.

Lemma rational_arctan_nonpos : ∀ r, 
  r ≤ 0 -> rational_arctan r ≤ 0.
Proof.
  intros ? Hle.
  rewrite <- arctan_Qarctan.
  apply arctan_nonpos.
  apply CRle_Qle.
  assumption.
Qed.


Lemma sin_o_arctan_nonneg : ∀ r, 0 ≤ r  →  0 ≤ sin (arctan r).
Proof.
  intros r Hle.
  apply CRSin_nonneg.
  pose proof (CRarctan_range r) as Harc.
  destruct Harc as [Harcl Harcr].
  pose proof (orders.strict_po_trans _ _ _ Harcr PiHalfLt).
  split;[| apply CRweakenLt; assumption].
  apply arctan_nonneg. assumption.
Qed.


Lemma sin_o_arctan_northeast: ∀ (cy cx : Q), 
    (0 ≤ cy)%Q → (0 < cx)%Q
    → 'cy = √ (cx * cx + cy * cy)%Q * sin (rational_arctan (cy/cx)).
Proof.
  intros ? ? Hy Hx.
  pose proof Hy as Hyr.
  pose proof Hx as Hxr.
  apply CRle_Qle in Hyr.
  rewrite <- arctan_Qarctan. apply EqIfSqrEqNonNeg; trivial;
        [apply orders.nonneg_mult_compat; unfold PropHolds;
          eauto using CRrational_sqrt_nonneg;[] |].
  apply sin_o_arctan_nonneg.
  apply CRle_Qle. revert Hx Hy. unfoldMC.
  intros. apply Qmult_le_r with (x:=0%Q) (y:=(cy / cx)%Q) in Hx.
  apply Hx. rewrite Qmult_0_l, Qmult_comm, Qmult_div_r.
  assumption; fail.
  revert Hxr. unfoldMC. lra.

  rewrite sqrProdRW.
  symmetry.
  rewrite rings.mult_comm.
  rewrite <- CRpower_N_2. 
  rewrite  arctan_Qarctan.
  unfold recip, dec_fields.recip_dec_field, dec_recip,
    stdlib_rationals.Q_recip, mult, stdlib_rationals.Q_mult.
    simpl. idtac. fold (Qdiv cy cx).
  assert ((cx ≠ 0 )) as Hneq by (unfoldMC; lra).
  rewrite sqr_o_sin_o_Qarctan_o_div;[|assumption].
  unfold sqrtFun, rational_sqrt_SqrtFun_instance.
  let rs := eval simpl in (CRsqrt_sqr1Q1 cx cy) in rewrite rs.
  autorewrite with MoveInjQCROut.
  apply inject_Q_CR_wd.
  unfoldMC. simpl. 
  field.
  intro Hc. apply Hneq.
  apply QSumOfSqr0Implies in Hc. assumption.
Qed.

Lemma CRarctan_odd : forall r : CR, arctan (-r) = - (arctan r).
Proof.
  intros r.
  pose proof (ArcTan_inv (CRasIR r)) as Hir.
  apply IRasCR_wd in Hir.
  autorewrite with IRtoCR in Hir.
  rewrite CRasIRasCR_id in Hir.
  exact Hir.
Qed.
  
Lemma CRQarctan_odd : forall r : Q, rational_arctan (-r) = - (rational_arctan r).
Proof.
  intros r.
  rewrite <- arctan_Qarctan.
  rewrite <- arctan_Qarctan.
  rewrite <- CRopp_Qopp.
  apply CRarctan_odd.
Qed.

Lemma sin_o_arctan_southeast: ∀ (cy cx : Q), 
    (cy ≤ 0)%Q → (0 < cx)%Q
    → 'cy = √ (cx * cx + cy * cy)%Q * sin (rational_arctan (cy/cx)).
Proof.
  intros ? ? Hy Hx.
  assert (0 ≤ (-cy)) as Hpos by (revert Hy; unfoldMC; lra).
  pose proof (sin_o_arctan_northeast (-cy) (cx) Hpos Hx) as Hp.
  idtac. assert (- cy / cx = - (cy / cx)) as Hdiv by 
    (unfoldMC;field; revert Hx; unfoldMC; lra).
  rewrite  Hdiv, CRQarctan_odd, CRSin_inv in Hp.
  rewrite <- CRopp_Qopp in Hp.
  clear Hdiv. 
  assert ((- cy * - cy)%Q = (cy * cy)%Q ) as Heq by 
    (unfoldMC; field).
  rewrite Heq in Hp. clear Heq. 
  revert Hp. unfoldMC. fold (Qdiv cy cx). 
  prepareForCRRing. intros. idtac. 
  apply CRopp_wd in Hp.
  assert ( (- - ' cy) [=]  ' cy)%CR as Hr by ring.
  rewrite Hr in Hp.
  rewrite Hp. ring.
Qed.

Lemma sin_o_arctan_east: ∀ (cy cx : Q), 
    (0 < cx)%Q
    → 'cy = √ (cx * cx + cy * cy)%Q * sin (rational_arctan (cy/cx)).
Proof.
  intros ? ? Hx.
  destruct (decide (0 < cy)) as [Hd | Hd];
    [apply sin_o_arctan_northeast | apply sin_o_arctan_southeast];
       try assumption; revert Hd; unfoldMC; intros; lra.
Qed.

Lemma QdivNegCancel : forall cx cy: Q,
  (cx ≠ 0)
  -> (- cy / - cx)%Q = (cy / cx)%Q.
Proof.
  intros ? ? H. unfoldMC.  idtac. idtac.
  field. exact H.
Qed.
  
Lemma cos_o_arctan_west: ∀ (cy cx : Q), 
  (cx < 0)%Q
  → ' cx = √ (cx * cx + cy * cy)%Q * - cos (rational_arctan (cy / cx)).
Proof.
  intros  ? ? Hneg.
  assert (0 < (-cx))%Q as Hpos by lra.
  assert (cx ≠ 0) as Hneq by (unfoldMC; lra).
  pose proof (cos_o_arctan_east (-cy) (-cx) Hpos) as Hp.
  idtac. rewrite QdivNegCancel in Hp by assumption.
  assert ((- cx * - cx + - cy * - cy)%Q = (cx * cx + cy * cy)%Q ) as Heq by 
    (unfoldMC; field).
  rewrite Heq in Hp. clear Heq.
  rewrite <- CRopp_Qopp in Hp.
  apply (injective CRopp).
  rewrite Hp.
  unfoldMC. ring.
Qed.

Lemma sin_o_arctan_west: ∀ (cy cx : Q), 
  (cx < 0)%Q
    → 'cy = √ (cx * cx + cy * cy)%Q * - sin (rational_arctan (cy/cx)).
Proof.
  intros  ? ? Hneg.
  assert (0 < (-cx))%Q as Hpos by lra.
  assert (cx ≠ 0) as Hneq by (unfoldMC; lra).
  pose proof (sin_o_arctan_east (-cy) (-cx) Hpos) as Hp.
  idtac. rewrite QdivNegCancel in Hp by assumption.
  assert ((- cx * - cx + - cy * - cy)%Q = (cx * cx + cy * cy)%Q ) as Heq by 
    (unfoldMC; field).
  rewrite Heq in Hp. clear Heq.
  rewrite <- CRopp_Qopp in Hp.
  apply (injective CRopp).
  rewrite Hp.
  unfoldMC. ring.
Qed.

Lemma CRLtAddLHS : forall (c a b : CR),
  a < b
  → c + a  < c + b.
Proof.
  intros  ? ? ?  Hab.
  apply orders.strictly_order_preserving; eauto with *.
Qed.

Lemma CRLtAddRHS : forall (c a b : CR),
  a < b
  → a+c < b+c.
Proof.
  intros  ? ? ?  Hab.
  rewrite rings.plus_comm.
  remember (c+a) as ac. rewrite rings.plus_comm.
  subst ac.
  apply CRLtAddLHS.
  trivial.
Qed.


Lemma CR_AbsSmall_as_IR: 
    ∀ x y : CR, AbsSmall x y ↔ AbsSmall (CRasIR x) (CRasIR y).
Proof.
  intros.
  pose proof (IR_AbsSmall_as_CR (CRasIR x) (CRasIR y)) as H.
  rewrite CRasIRasCR_id in H.
  rewrite CRasIRasCR_id in H.
  tauto.
Qed.

Lemma CR_minus_asIR: ∀ x y : CR, CRasIR (x - y) [=] CRasIR x[-]CRasIR y.
Proof.
  intros.
  unfold cg_minus. simpl.
  rewrite  CR_plus_asIR, CRasIR_inv.
  reflexivity.
Qed.

Lemma CR_minus_asIR2: ∀ x y : CR, CRasIR (x [-] y) [=] CRasIR x[-]CRasIR y.
Proof.
  intros. apply CR_minus_asIR.
Qed.

Lemma ProperCRsqrt : Proper (equiv ==> equiv) CRsqrt.
Proof using.
 intros ? ? H1.
 rewrite H1.
 reflexivity.
Qed.

Lemma rational_arctan_increasing : forall a b:Q,
(a <= b)%Q
→ (rational_arctan a <= rational_arctan b)%CR.
Proof.
  intros ? ? Hab.
  rewrite  <- arctan_Qarctan.
  rewrite  <- arctan_Qarctan.
  apply CRArcTan_resp_leEq.
  apply CRle_Qle.
  exact Hab.
Qed.

Lemma CRasIRless : ∀ x y:CR,
 (CRasIR x [<] CRasIR y IFF  x <  y).
Proof.
  intros  ? ?.
  split; intro H.
  - rewrite <- CRasIRasCR_id.
    setoid_rewrite <- CRasIRasCR_id at 3.
    apply CR_lt_ltT.
    apply IRasCR_preserves_less. assumption.
  - rewrite <- CRasIRasCR_id in H.
    setoid_rewrite <- CRasIRasCR_id at 3 in H.
    apply CR_less_as_IR.
    apply CR_lt_ltT.
    assumption.
Qed.

  
Lemma CRArcTan_resp_less : ∀ x y, (x < y -> arctan x < arctan y).
Proof.
  intros ? ? Hless.
  apply CRasIRless in Hless.
  pose proof (ArcTan_resp_less (CRasIR x) (CRasIR y) Hless) as Hir.
  eapply less_wdl in Hir; [| symmetry; apply arctan_correct_CR].
  eapply less_wdr in Hir; [| symmetry; apply arctan_correct_CR].
  apply CRasIRless in Hir.
  assumption.
Qed.


Lemma rational_arctan_increasing_strict : forall a b:Q,
(a < b)%Q
→ (rational_arctan a < rational_arctan b)%CR.
Proof.
  intros ? ? Hab.
  apply CR_lt_ltT.
  rewrite  <- arctan_Qarctan.
  rewrite  <- arctan_Qarctan.
  apply CRArcTan_resp_less.
  apply CR_lt_ltT.
  apply CRlt_Qlt.
  assumption.
Qed.


(*
Definition badapproxNum (r: CR) (den : positive) : Z:=
  let q:= (approximate r (QposMake 1 den)) in
  (Zdiv ( (Qnum q)*den) (Qden q)).

Definition badApproximate (r: CR) (den : positive) : Q:=
  let q:= (approximate r (QposMake 1 den)) in
  (Zdiv ((Qnum q)*den) (Qden q)).
*)

Open Scope Q_scope.

Require Import Coq.QArith.Qround.

Definition Q2Zapprox (q : Q) : Z :=
  let qf := Qfloor q in
  if (decide (Qle (q - qf) (1#2)))
    then qf
    else (qf+1)%Z.


Require Import CoRN.model.metric2.Qmetric.

Lemma Q2ZapproxSpec: ∀ (q:Q),
  Qball (QposMake 1 2) q (Q2Zapprox q).
Proof.
  intros.
  unfold Qball.
  unfold AbsSmall.
  simpl.
  unfold Q2Zapprox.
  destruct (decide (q - Qfloor q <= 1 # 2)) as [Hd | Hd].
- split; [| lra].
  pose proof (Qfloor_le q) as Hq.
  lra.
- pose proof (Qlt_floor q) as Hq.
  split; try lra.
  assert (q - Qfloor q > 1 # 2) as Ht by lra.
  clear Hd.
  rewrite inject_Z_plus.
  unfold inject_Z.
  simpl. clear Hq. 
  unfold inject_Z in Ht.
  lra.
Qed.

(** This might be of general interest to CoRN *)
Definition R2ZApprox (r: CR) (eps : Qpos) : Z :=
  Q2Zapprox (approximate r eps).

Lemma R2ZApproxSpec : ∀ (r: CR) (eps : Qpos), 
  ball (eps + (QposMake 1 2)) r (''(R2ZApprox r eps)).
Proof.
  intros ? ?.
  pose proof (ball_approx_r r eps ) as Hball.
  pose proof (Q2ZapproxSpec (approximate r eps)) as Hq.
  eapply ball_triangle; eauto.
  unfold cast, stdlib_rationals.inject_Z_Q.
  unfold R2ZApprox.
  apply ball_Cunit.
  exact Hq.
Qed.


Close Scope Q_scope.

Global Instance : Cast positive CR :=
  (cast Q CR) ∘ (cast Z Q) ∘ (Zpos).


Definition simpleApproximate (r: CR) (den : positive) (eps : Qpos): Q:=
  Qmake (R2ZApprox (r * '(den)) eps)  den.

Lemma ballDiv : ∀ (r1 r2 : CR) (d : positive) (qp : Qpos),
  ball qp r1 r2
  → ball (qp/d) (r1 * '(/inject_Z d)) (r2 * '(/ inject_Z  d)).
Proof.
  intros ? ? ? ? Hb.
  unfold ball.
  simpl. apply CRAbsSmall_ball.
  unfold mult.
  rewrite <- ring_distl_minus.
  unfold cast.
  idtac. simpl.
  rewrite <- CRmult_Qmult.
  apply mult_AbsSmall.
- apply CRAbsSmall_ball. assumption.
- apply AbsSmall_reflexive.
  apply CRle_Qle.
  unfoldMC.
  unfold Qinv.  simpl.
  unfold Qle.
  simpl.
  omega.
Qed.

Lemma ringMultDiv : ∀ (a b c : CR),
  b * c = 1
  -> a = a* b* c.
Proof.
  intros ? ? ? H.
  rewrite <- sr_mult_associative.
  rewrite H.
  prepareForCRRing.
  ring.
Qed.

(* Move to numericalOpt *)
Lemma simpleApproximateSpec : ∀ (r: CR) (den : positive) (eps : Qpos), 
  ball ((eps + (QposMake 1 (2)))/den) r ('simpleApproximate r den eps).
Proof.
  intros ? ? ?.
  unfold simpleApproximate.
  pose proof (R2ZApproxSpec (r * ' den) eps) as Hb.
  apply ballDiv with (d:=den) in Hb.
  idtac.
  eapply ball_wd;[reflexivity | | | apply Hb]; auto.
- apply ringMultDiv.
  unfold cast, Cast_instance_0.
  unfold cast.
  unfold stdlib_rationals.inject_Z_Q, Basics.compose.
  rewrite CRmult_Qmult.
  apply inject_Q_CR_wd.
  unfoldMC. field.
  auto using Q.positive_nonzero_in_Q.
- unfold cast.
  unfold cast, Cast_instance_0.
  unfold cast.
  unfold stdlib_rationals.inject_Z_Q, Basics.compose.
  rewrite CRmult_Qmult.
  apply inject_Q_CR_wd.
  unfold dec_recip, stdlib_rationals.Q_recip.
  unfoldMC.
  remember (R2ZApprox (r * ' den)%CR eps) as hh.
  rewrite Qmake_Qdiv.
  reflexivity.
Qed.

Open Scope Qpos_scope.
Definition simpleApproximateErr (res : positive) (eps : Qpos) : Qpos :=
  ((eps + (QposMake 1 (2)))/ res).
Close Scope Qpos_scope.

Notation tapprox := simpleApproximate.

Definition approximateAngleAsDegrees (a:CR) : Z :=
 R2ZApprox (a*CRPiInv* ('180%positive)) (QposMake 1 100).

Lemma CRNotLeLtDN : forall (a b : CR),
not (a < b)
-> util.DN (b ≤ a).
Proof.
  intros ? ? Hl Hd.
  pose proof (CRle_lt_dec b a) as Hdn.
  apply Hdn. intro Hdd. clear Hdn.
  destruct Hdd;[tauto|].
  apply CR_lt_ltT in c.
  tauto.
Qed.

Lemma CRapproxMax : forall (eps:Qpos) (a b : CR),
(approximate (CRmax a b) eps)
  = QMinMax.Qmax (approximate a ((1 # 2) * eps)%Qpos)
  (approximate b ((1 # 2) * eps)%Qpos).
Proof using.
  intros ? ?. reflexivity.
Qed.

(** can this be faster in some cases? *)
Definition CRmax' (eps:Qpos) (a b : CR) : CR :=
match (CR_epsilon_sign_dec eps (b-a)) with
| Datatypes.Gt => b
| Datatypes.Lt => a
| Datatypes.Eq => CRmax a b
end.

(* Move *)
Lemma twoHalfCR :
½ * 2 = (1:CR).
Proof using.
  unfold half_num, CR_Half_instance.
  fold (cast Q CR).
  rewrite commutativity.
  rewrite <- RingProp3.
  rewrite <- preserves_plus.
  apply inject_Q_CR_wd.
  compute. reflexivity.
Qed.

(* Move *)
Lemma halfLeShift (a b:CR):  
2 * a ≤ b
↔
a ≤ ½* b.
Proof using.
  apply FieldLeRecipMultIff;
    [apply lt_0_2|].
  apply twoHalfCR.
Qed.

(** Move, and perhaps generalize for all completions of metric spaces *)
Definition lowerApprox (c:CR) (e:Qpos) : Q :=
  (approximate c e - `e).

Lemma addRangeLe : ∀ a t b v : CR, 
  (a - v) ≤ t  ≤ (b - v) → a ≤ t + v ≤ b.
Proof using.
  intros ? ? ? ? Hb.
  destruct Hb.
  split.
- apply shift_leEq_plus. assumption.
- apply shift_plus_leEq. assumption.
Qed.

Lemma pos_cos_CR : 
  ∀ θ : CR, 0 ≤ θ < (½ * π) → 0 < cos θ.
Proof using.
  intros ? Hbw.
  apply CRasIRless.
  eapply less_wdr; [| symmetry; apply cos_correct_CR].
  eapply less_wdl; [| symmetry; apply CRasIR0].
  rewrite CRPiBy2Correct1 in Hbw.
  rewrite <- IR_Zero_as_CR in Hbw.
  rewrite <- (CRasIRasCR_id θ) in Hbw.
  destruct Hbw as [Hbwl Hbwr].
  apply CR_lt_ltT in Hbwr.
  apply pos_cos;[ apply IR_leEq_as_CR| apply CR_less_as_IR]; assumption.
Qed.

Section Opt.
(** we need to often compare reals. This can
 -only be done upto a finte (but arbitrary) accuracy.*)
Variable eps : Qpos.
 
Definition approxDecLtRQ (a:CR) (b:Q) : bool :=
let aq : Q := approximate a eps in
bool_decide (aq + eps < b).

Require Import MathClasses.implementations.bool.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.orders.

Lemma approxDecLtRQSound: forall (a:CR) (b:Q),
approxDecLtRQ a b = true
→ a < 'b.
Proof using.
  intros ? ? H.
  apply bool_decide_true in H.
  eapply le_lt_trans;
    [apply upper_CRapproximation with (e:=eps)|].
  apply (@strictly_order_preserving _ _ _ _ _  _ _ _).
  exact H.
Qed.

Lemma approxDecLtRQApproxComplete: forall (a:CR) (b:Q),
a < '(b - 2*`eps)
→ approxDecLtRQ a b = true.
Proof using.
  intros ? ? H.
  apply bool_decide_true.
  rewrite preserves_minus in H.
  apply flip_lt_minus_l  in H.
  rewrite negate_involutive in H.
  apply (@strictly_order_reflecting _ _ _ _ _
      _ (@cast Q CR _) _).
  eapply le_lt_trans;[| apply H]. clear H.
  apply flip_le_minus_l.
  eapply transitivity;
    [|apply lower_CRapproximation with (e:=eps)].
  rewrite <- (@preserves_minus Q _ _ _ _ _ _ _ 
        CR _ _ _ _ _ _ _ _ _).
  apply (@order_preserving _ _ _ _ _
      _ (@cast Q CR _) _).
  apply eq_le. 
  autounfold with QMC.
  destruct eps. simpl.
  ring.
Qed.

Require Import CoRN.logic.Stability.

  
Lemma approxDecLtRQApproxFalse: forall (a:CR) (b:Q),
approxDecLtRQ a b = false
→ '(b - 2*`eps) ≤ a .
Proof using.
  intros ? ? H.
  apply stable.
  apply not_true_iff_false in H.
  apply CRNotLeLtDN.
  intro Hc.
  apply H. 
  apply approxDecLtRQApproxComplete.
  assumption.
Qed.

Definition approxDecLtRR (a b :CR) : bool :=
approxDecLtRQ (a-b) (0)%mc.


Lemma approxDecLtRRSound: forall (a b:CR),
approxDecLtRR a b = true
→ a < b.
Proof using.
  intros ? ?.
  unfold approxDecLtRR.
  intro H.
  apply approxDecLtRQSound in H.
  rewrite (@preserves_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _) in H.
  apply flip_lt_minus_l in H.
  rewrite plus_0_l in H.
  exact H.
Qed.

Lemma approxDecLtRRApproxComplete: forall (a b:CR),
a < b - '(2*`eps)
→ approxDecLtRR a b = true.
Proof using.
  intros ? ? H.
  apply approxDecLtRQApproxComplete.
  apply flip_lt_minus_l.
  rewrite preserves_minus.
  rewrite preserves_0.
  rewrite plus_0_l.
  rewrite (@commutativity _ _ _ plus _ _ _).
  exact H.
Qed.

Lemma approxDecLtRRApproxFalse: forall (a b:CR),
approxDecLtRR a b = false
→ b - '(2*`eps)  ≤ a.
Proof using.
  intros ? ? H.
  apply approxDecLtRQApproxFalse in H.
  rewrite preserves_minus in H.
  rewrite preserves_0 in H.
  rewrite plus_0_l in H.
  apply flip_le_minus_r in H.
  rewrite (@commutativity _ _ _ plus _ _ _) in H.
  exact H.
Qed.
End Opt.

Section TempRing.
Add Ring tempRingCR : (stdlib_ring_theory CR).

(** Move, and perhaps generalize for all completions of metric spaces *)
Lemma lowerApproxCorrect (c:CR) (e:Qpos):
  c-'(2*`e)  ≤ '(lowerApprox c e) ≤ c.
Proof using.
  unfold lowerApprox.
  setoid_rewrite (@preserves_minus Q _ _ _ _ _ _ _ CR 
    _ _ _ _ _ _ _ (cast Q CR) _).
  rewrite preserves_mult.
  rewrite preserves_2.
  rewrite <- RingProp3.
  apply addRangeLe.
  rewrite negate_involutive.
  match goal with
  [|- ?l ≤ _ /\ _] => ring_simplify l
  end.
  split;
    [|apply in_CRball; apply ball_approx_r].
  apply (fun b => proj1 ((proj2 (in_CRball e c _)) b)).
  apply ball_approx_r.
Qed.

End TempRing.

Lemma CRcos_resp_leEq: 
∀ x y : CR, 0 ≤ x → y ≤ π → x ≤ y → cos y ≤ cos x.
Proof using.
  intros ? ? H1 H2 H3.
  pose proof (Cos_resp_leEq (CRasIR x) (CRasIR y)) as Hc.
  apply CR_leEq_as_IR.
  autorewrite with CRtoIR.
  rewrite <- (IRasCRasIR_id Pi) in Hc.
  rewrite <- (IRasCRasIR_id [0]) in Hc.  
  apply Hc;clear Hc; apply CR_leEq_as_IR; auto;
  autorewrite with IRtoCR; auto.
Qed.


Lemma approximateLe : forall (a b : CR) (eps : Qpos),
approximate a eps ≤ approximate b eps
→ a - ' (2 * ` eps) ≤ b.
Proof using.
  intros ? ?  ? H.
  eapply transitivity;
    [|apply lower_CRapproximation with (e:=eps)].
  apply flip_le_minus_l.
  eapply transitivity;
    [apply upper_CRapproximation with (e:=eps)|].
  fold ((@cast Q (st_car (msp_is_setoid CR)) inject_Q_CR)).
  rewrite <- (@preserves_plus Q CR _ _ _ _ _ _ _ _ _ _ _ _ _ ).
  apply (@order_preserving _ _ _ _ _ _ _ _ _ _).
  simpl.
  autounfold with QMC in *.
  remember (approximate a eps).
  remember (approximate b eps).
  destruct eps.
  simpl in *.
  lra.
Qed.