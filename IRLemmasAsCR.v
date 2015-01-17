
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

(*Instance castCRIR : Cast CR IR := CRasIR. *)
