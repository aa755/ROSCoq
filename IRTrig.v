Require Export CoRN.transc.ArTanH.
Require Export CoRN.transc.SinCos.
Require Export CoRN.transc.PowerSeries.
Require Export CoRN.transc.Pi.
Require Export CoRN.transc.TrigMon.
Require Export CoRN.transc.MoreArcTan.
Require Export CoRN.transc.Exponential.
Require Export CoRN.transc.InvTrigonom.
Require Export CoRN.transc.RealPowers.
Require Export CoRN.transc.Trigonometric.
Require Export CoRN.transc.TaylorSeries.

Require Import Coq.Unicode.Utf8.

Local Opaque Sine  Cosine.

Lemma DomTangCosNZ : forall θ,
    Dom Tang θ IFF Dom (f_rcpcl' IR) (Cos θ).
Proof.
  unfold Tang. simpl.
  Local Transparent Sine.
  simpl. unfold extend, conjP. intros. simpl.
  Local Transparent Cosine.
  split; intro H; 
    [destruct H as [? H]; destruct H as [H Hc]| split;[|split]];
    try tauto; try apply Hc.
- simpl. auto.
- intros. eapply ap_wd; eauto;[| reflexivity].
  apply pfwdef. reflexivity.
Qed.

Local Opaque Sine  Cosine.
Lemma DomTangCosSqNZ : forall θ,
    Dom Tang θ IFF Dom (f_rcpcl' IR) ((Cos θ)[^]2).
Proof.
  unfold Tang. simpl.
  Local Transparent Sine.
  simpl. unfold extend, conjP. intros. simpl.
  Local Transparent Cosine.
  split; intro H; 
    [destruct H as [? H]; destruct H as [H Hc]| split;[|split]];
    try tauto; try apply Hc.
- specialize (Hc I). 
  pose proof (mult_resp_ap_zero _ _ _  Hc Hc) as Hx.
  eapply ap_wd; eauto;[| reflexivity].
  rational.
- simpl. auto.
- intros. apply mult_cancel_ap_zero_rht in H.
  eapply ap_wd; eauto;[| reflexivity].
  apply pfwdef. reflexivity.
Qed.

Lemma cr_div_shiftr :
  forall {F: CField} (x y z : F) zp,
  z [#] [0]
  -> (x [*] z [=] y <-> x [=] (y [/] z [//] zp)).
Proof.
  intros ? ? ? ? ? Hzp. split; intros Hm.
- apply mult_cancel_rht with (z:= z) ; trivial.
  rewrite div_1.
  trivial.
- apply mult_wdl with (y:=z) in Hm.
  rewrite div_1 in Hm.
  trivial.
Qed.

  
Lemma CosSqrFromTan1 : forall θ Hx H, 
    Cos θ[^]2 [=] ([1][/] ([1][+]Tan θ Hx[^]2)[//]H).
Proof.
  intros.
  pose proof (DomTangCosSqNZ θ) as Hd.
  apply fst in Hd. specialize (Hd Hx).
  pose proof (FFT' θ Hx Hd) as Hf.
  apply cr_div_shiftr; eauto;[].
  apply cr_div_shiftr in Hf; eauto;[].
  rewrite mult_commutes. trivial.
Qed.

Lemma CosOfArcTan : forall r H,
    Cos (ArcTan r)[^]2 [=] ([1][/] ([1][+]r[^]2)[//]H).
Proof.
  intros.
  rewrite CosSqrFromTan1.
  apply cr_div_shiftr; eauto;[].
  symmetry.
  rewrite mult_commutes.
  rewrite x_mult_y_div_z.
  apply cr_div_shiftr; eauto;
  [|rewrite <- Tan_ArcTan; rational; fail].
  eauto using 
    zero_minus_apart,
    ap_wdl_unfolded,
    zexp_resp_ap_zero,
    zexp_one.
  Grab Existential Variables.
- simpl. simpl in H. eapply ap_wd; eauto;[| reflexivity].
  rewrite <- Tan_ArcTan; rational.
- simpl. simpl in H. eapply ap_wd; eauto;[| reflexivity].
  rewrite <- Tan_ArcTan; rational.
- apply Dom_Tang_ArcTan.
Qed.


Lemma SinOfArcTan : forall r H,
    Sin (ArcTan r)[^]2 [=] (r[^]2[/] ([1][+]r[^]2)[//]H).
Proof.
  intros.
  pose proof (CosOfArcTan r H) as Hc.
  pose proof (FFT (ArcTan r)) as Hf.
  pose proof (cg_minus_wd _ _ _ _ _ Hf Hc) as Hm.
  clear Hf Hc.
  match goal with
  [H:st_eq ?l _ |- st_eq ?lg _] => assert (l [=] lg) as Heq
      by (rational); rewrite Heq in Hm; clear Heq
  end.
  rewrite Hm.
  apply cr_div_shiftr; eauto.
  rewrite ring_distr2.
  rewrite div_1.
  rational.
Qed.
