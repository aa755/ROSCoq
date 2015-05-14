Require Export CoRN.metric2.ProductMetric.
Require Export CoRN.metric2.UniformContinuity.
Require Export CoRN.metric2.StepFunction.
Require Export CoRN.metric2.Limit.
Require Export CoRN.metric2.Hausdorff.
Require Export CoRN.metric2.StepFunctionMonad.
Require Export CoRN.metric2.Classification.
Require Export CoRN.metric2.CompleteProduct.
Require Export CoRN.metric2.Prelength.
Require Export CoRN.metric2.UCFnMonoid.
Require Export CoRN.metric2.Complete.
Require Export CoRN.metric2.ProductMetric.
Require Export CoRN.metric2.Metric.
Require Export CoRN.metric2.MetricMorphisms.
Require Export CoRN.metric2.StepFunctionSetoid.
Require Export CoRN.metric2.DistanceMetricSpace.
Require Export CoRN.metric2.FinEnum.
Require Export CoRN.metric2.Compact.
Require Export CoRN.metric2.Graph.
Require Export CoRN.metric2.CompletePointFree.
Require Export CoRN.metrics.IR_CPMSpace.
Require Export CoRN.metrics.ContFunctions.
Require Export CoRN.metrics.Equiv.
Require Export CoRN.metrics.CPseudoMSpaces.
Require Export CoRN.metrics.CMetricSpaces.
Require Export CoRN.metrics.Prod_Sub.

Require Export Coq.Unicode.Utf8.



Section OldNew.
  Variable (R : CMetricSpace).
 (** Our goal is to create an instance of metric2.MetricSpace,
    the new theory fo metric spaces *)

Definition fromOldMetricTheory :MetricSpace.
  destruct R.
  destruct scms_crr.
  destruct cms_crr.
  simpl in ax_d_apdiag_imp_grzero, cms_proof,cms_d .
  apply Build_MetricSpace with (msp_is_setoid := cs_crr)
    (ball := λ (eps : Qpos) a b, (cms_d a b) [<=] inj_Q IR (QposAsQ eps) ).
- intros. rewrite H0,H1.
  apply (inj_Q_wd IR) in H.
  rewrite H. reflexivity.
- destruct cms_proof.
  constructor; simpl; auto.
  + unfold Reflexive. intros.
    unfold pos_imp_ap in ax_d_pos_imp_ap.
    simpl in ax_d_pos_imp_ap.
    
  




