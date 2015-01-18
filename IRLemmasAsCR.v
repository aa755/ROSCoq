
Require Export CoRN.reals.fast.CRtrans.
(* Require Export CoRN.reals.faster.ARbigD. *)
(* Require Export CoRN.ftc.IntegrationRules. *)

Require Export Coq.Program.Tactics.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.
Require Export MathClasses.interfaces.abstract_algebra.


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

Hint Rewrite CRasIR0 CRasIR_inv : CRtoIR .

Require Import  MathClasses.interfaces.additional_operations.

Ltac prepareForCRRing := 
  unfold zero, one, CR1, stdlib_rationals.Q_0, mult, cast,
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
  eq a b -> a == b.
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

Lemma inject_Q_CR_one  : (inject_Q_CR (1#1) [=] 1)%CR.
ring.
Qed.

Lemma inject_Q_CR_two  : (inject_Q_CR (2#1) = 2)%CR.
  rewrite <- inject_Q_CR_one.
  destruct CR_Q_ring_morphism.
  idtac. unfold plus, CRplus. rewrite <- morph_add; eauto.
Qed.

Definition QCRM := CR_Q_ring_morphism.

Lemma CR_Cos_HalfPi : (cos (CRpi * ' (1 # 2)) = 0 )%CR.
Proof.
  pose proof (Pi.Cos_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <- Hc.
  apply sm_proper.
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
  generalize (inject_Q_CR(1 # 2)).
  intros.  CRRing. 
Qed.

Lemma CRCos_plus_Pi: ∀ x : CR, cos (x + CRpi) = - (cos x).
  intros x.
  pose proof (Pi.Cos_plus_Pi (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  exact Hc.
Qed.

Lemma CRSin_plus_Pi: ∀ x : CR, sin (x + CRpi) = (- sin x).
  intros x.
  pose proof (Pi.Sin_plus_Pi (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  exact Hc.
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



Lemma cosArcTan : forall (cx cy: CR) xnz ,
CRsqrt (cx * cx + cy * cy) 
* (cos (arctan (cy // (cx ↾ xnz)))) = cx.
Proof.
  intros ? ?.
Abort.
(*Instance castCRIR : Cast CR IR := CRasIR. *)
