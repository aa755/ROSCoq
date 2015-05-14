Require Export CoRN.metric2.Metric.
Require Export CoRN.metrics.CMetricSpaces.

Require Export Coq.Unicode.Utf8.

Lemma QposIRPosQ0 : ∀ (qp : Qpos), 
  inj_Q IR [0] [<] inj_Q IR (QposAsQ qp).
Proof.
  intros.
  destruct qp.
  apply inj_Q_less.
  simpl.
  auto.
Qed.

Lemma QposIRPos : ∀ (qp : Qpos), 
  [0] [<] inj_Q IR (QposAsQ qp).
Proof.
  intros.
  eapply less_wdl;[apply QposIRPosQ0|].
  apply inj_Q_Zero.
Qed.

Section OldNew.
  Variable (R : CMetricSpace).
 (** Our goal is to create an instance of metric2.MetricSpace,
    the new theory fo metric spaces *)

Require Export Psatz.

Definition fromOldMetricTheory :MetricSpace.
  apply Build_MetricSpace with (msp_is_setoid := R)
    (ball := λ (eps : Qpos) a b, (a[-d] b) [<=] inj_Q IR (QposAsQ eps)).
- intros. rewrite H0,H1.
  apply (inj_Q_wd IR) in H.
  rewrite H. reflexivity.
- constructor.
  + unfold Reflexive. intros.
    apply leEq_def.
    intros Hc.
    eapply less_transitive_unfolded in Hc;
      [| apply QposIRPos].
    apply ax_d_pos_imp_ap in Hc;[| apply cms_proof].
    eauto 2 with *.
    apply ap_irreflexive_unfolded in Hc.
    assumption.
  + unfold Symmetric. intros.
    rewrite ax_d_com;[| apply cms_proof].
    assumption.
  + intros. rewrite Q_Qpos_plus.
    rewrite inj_Q_plus.
    pose proof (plus_resp_leEq_both _ _ _ _ _ H H0) as Hadd.
    clear H H0.
    eapply leEq_transitive;[| apply Hadd].
    apply ax_d_tri_ineq.
    apply cms_proof.
  + intros.
    apply leEq_def.
    intros Hc.
    pose proof Hc as Hcb.
    apply Q_dense_in_CReals' in Hc.
    destruct Hc as [qb Hc].
    apply less_inj_Q in Hc.
    simpl in Hc.
    simpl in qb.
    assert (0 < qb - e)%Q as qbp by (destruct e; simpl; simpl in Hc;lra).
    specialize (H (mkQpos qbp)).
    pose proof (less_leEq_trans _ _ _ _ c H) as Hcc.
    revert Hcc Hc.
    clear.
    intros Hcc Hc.
    apply less_inj_Q in Hcc.
    simpl in Hcc.
    destruct e.
    simpl in *.
    lra.
  + intros.
    apply d_zero_imp_eq.
    assert ([0] [<=] a[-d]b) as Hnz by 
      (apply ax_d_nneg; apply cms_proof).
    remember (a[-d]b) as dab. clear dependent a.
    clear dependent  b. symmetry.
    (* this subgoal could be a generally useful lemma*)
    rewrite <- inj_Q_Zero.
    rewrite <- inj_Q_Zero in Hnz.
    apply not_ap_imp_eq.
    intros Hc.
    eapply leEq_not_eq in Hnz; eauto.
    clear Hc. rename Hnz into Hc.
    apply Q_dense_in_CReals' in Hc.
    destruct Hc as [qb Hc].
    apply less_inj_Q in Hc.
    simpl in Hc.
    simpl in qb.
    assert (0 < qb)%Q as qbp by (lra).
    specialize (H (mkQpos qbp)).
    apply leEq_def in H; auto.
Qed.

End OldNew.