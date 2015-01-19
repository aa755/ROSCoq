
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


Hint Rewrite CRasIR0 CRasIR_inv CR_mult_asIR 
  CR_plus_asIR CRpower_N_asIR: CRtoIR .


Ltac prepareForCRRing := 
  unfold zero, one, CR1, stdlib_rationals.Q_0, mult, cast,
  plus, CRplus,
  canonical_names.negate.

Ltac CRRing :=
    prepareForCRRing;
    let H:= fresh "H" in
    match goal with
    [|-equiv ?l ?r] => assert (st_eq l  r) as H by ring;
                       rewrite <- H; clear H; reflexivity
    end.

Require Import Coq.QArith.Qfield.
Require Import Coq.QArith.Qring.
Require Import Psatz.

Lemma eq_implies_Qeq: forall a b : Q,
  eq a b -> Qeq a b.
Proof.
  intros ? ?  H. rewrite H.
  reflexivity.
Qed.
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
  intros. rewrite <- cos_correct_CR, <- cos_correct_CR.
  apply IRasCR_wd.
  rewrite <- SinCos.Cos_inv.
  apply SinCos.Cos_wd.
  
  pose proof (Pi.Cos_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <-  CRasIR_inv.
  apply CRasIR_wd.
  ring.
Qed.

Lemma multNegShiftOut : forall a s : CR ,
(a * - s)%CR = (- (a * s))%CR.
Proof.
  intros. CRRing.
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
  intros. rewrite <- sin_correct_CR, <- sin_correct_CR.
  rewrite <- IR_opp_as_CR.
  apply IRasCR_wd.
  rewrite <- SinCos.Sin_inv.
  apply SinCos.Sin_wd.
  
  pose proof (Pi.Cos_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <-  CRasIR_inv.
  apply CRasIR_wd.
  ring.
Qed.

Lemma CREquiv_st_eq: forall a b : CR,
  st_eq (r:=CR) a  b <-> a = b.
Proof.
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

Class RealNumberPi (R : Type) := π : R.
Instance CRpi_RealNumberPi_instance : RealNumberPi CR := CRpi.

Class HalfNum (R : Type) := half_num : R.
Notation "½" := half_num.
Instance Q_Half_instance : HalfNum Q := (1#2).
Instance CR_Half_instance : HalfNum CR := (inject_Q_CR (1#2)).

Close Scope Q_scope.

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


Lemma sin_correct_CR : forall x,
  CRasIR (sin x) = (PowerSeries.Sin (CRasIR x)).
Proof.
  intros x. apply (injective IRasCR). rewrite sin_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.

Lemma cos_correct_CR : forall x,
  CRasIR (cos x) = (PowerSeries.Cos (CRasIR x)).
Proof.
  intros x. apply (injective IRasCR). rewrite cos_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.

Lemma arctan_correct_CR : forall x,
  CRasIR (arctan x) = (ArcTan (CRasIR x)).
Proof.
  intros x. apply (injective IRasCR). rewrite arctan_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.

Hint Rewrite sin_correct_CR cos_correct_CR : CRtoIR.

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

Require Export CoRN.reals.R_morphism.



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

Require Export IRTrig.


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

Lemma CRApart_wdl :forall a b c:CR, 
  a = b -> a ≶ c -> b ≶ c.
Proof.
  intros ? ? ? Heq.
  apply strong_setoids.apart_proper; auto.
Qed.


Lemma  OnePlusSqrPos : forall r:CR, (1 + r ^ 2) ≶ 0.
Proof.
  intros.
  symmetry.
  apply orders.lt_iff_le_apart.
  apply semirings.pos_plus_le_lt_compat_l; auto.
  simpl. apply semirings.lt_0_1.
  apply CR_leEq_as_IR.
  autorewrite with CRtoIR.
  apply sqr_nonneg.
Qed.

Definition mkCr0' (a : CR) (ap : (a ≶ 0)%CR)  : CR ₀ :=
   (a ↾ ap).

Lemma sqr_o_cos_o_arctan2 : forall r,
    (cos (arctan r)) ^2 = (1 //(mkCr0' (1 + r^2) (OnePlusSqrPos _))).
Proof.
  intros. apply sqr_o_cos_o_arctan.
Qed.

Lemma sqr_o_sin_o_arctan2 : forall r,
    (sin (arctan r)) ^2 = (r^2 //(mkCr0' (1 + r^2) (OnePlusSqrPos _))).
Proof.
  intros. apply sqr_o_sin_o_arctan.
Qed.

