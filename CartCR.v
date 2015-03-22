
Require Export CoRN.reals.fast.CRtrans.
(* Require Export CoRN.reals.faster.ARbigD. *)
(* Require Export CoRN.ftc.IntegrationRules. *)

Require Export Coq.Program.Tactics.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.
Require Export IRLemmasAsCR.


Definition QSignHalf (q: Q) : Q :=
  QSign q ½ .

Require Export Vector.
Local Notation yes := left.
Local Notation no := right.

Definition polarTheta (cart :Cart2D Q) : CR :=
  if (decide ((X cart) = 0)) 
    then
      CRpi * ' QSignHalf (Y cart)
    else
      let angle := (rational_arctan (Y cart / (X cart))) in
      if decide (X cart < 0) then angle + (QSign (Y cart) π) else angle.


Definition polarθSign (target : Cart2D Q) : Q := QSign (Y target) 1.

Definition Cart2Polar (cart :Cart2D Q) : Polar2D CR :=
  {|rad := ( |cart| )  
  ; θ := polarTheta cart |}.


Definition Polar2Cart (pol : Polar2D CR) : Cart2D CR :=
  {|X := (rad pol) * (cos (θ pol)) 
  ; Y := (rad pol) * (sin (θ pol)) |}.


Require Import Coq.QArith.Qfield.
Require Import Coq.QArith.Qring.
Require Import Psatz.


Lemma Cart2Polar2CartID : forall (c :Cart2D Q),
  ' c = Polar2Cart (Cart2Polar c).
Proof.
  intros c.
  unfold Cart2Polar, Polar2Cart.
  simpl. destruct c as [cx cy].
  unfold polarTheta. simpl.
  destruct (decide (cx = 0)) as [Hcx0 | Hcx0];
  unfold equiv,EquivCart,CanonicalNotations.norm, NormSpace_instance_Cart2D ; simpl;[|].
- rewrite Hcx0. prepareForCRRing.
  unfold stdlib_rationals.Q_mult, stdlib_rationals.Q_plus. QRing_simplify.
  simpl. rewrite CRrational_sqrt_ofsqr.
  unfold QSignHalf, QSign.
  destruct (decide (cy < 0)) as [Hlt | Hlt];
    autorewrite with CRSimpl; 
  prepareForCRRing; try rewrite (morph_opp QCRM);
  split; CRRing.
- destruct (decide (cx < 0)) as [HcxNeg | HcxNeg].
  + rewrite  CRCos_PlusMinus_Pi,  CRSin_PlusMinus_Pi. split;
    [apply cos_o_arctan_west| apply sin_o_arctan_west]; assumption.
  + apply orders.full_pseudo_srorder_le_iff_not_lt_flip in HcxNeg.
    apply CRle_Qle in HcxNeg.
    split; [apply cos_o_arctan_east |  apply sin_o_arctan_east];
       apply CRle_Qle in HcxNeg; revert Hcx0 HcxNeg;
        unfoldMC; intros; lra.
Qed.

Require Export orders.

Hint Resolve CRweakenLt CRLtAddLHS CRLtAddRHS : CRBasics.

(*
Lemma polarθSignCorr : ∀ targetPos,
 0 < polarTheta targetPos ↔  0 < (Y targetPos).
Proof.
  intros. unfold polarθSign, polarTheta.
  destruct (decide (X targetPos = 0)); auto.
- unfold QSignHalf.
-   
*)

Lemma CRabsCRpi : CRabs CRpi = CRpi.
  rewrite CRabs_pos;[reflexivity|].
  apply CRweakenLt.
  apply CR_lt_ltT.
  apply CRpi_pos.
Qed.

Instance NormSpace_instance_Q : NormSpace Q Q := Qabs.Qabs.


Lemma QAbsQSign : 
  ∀ a c,  (|QSign a c|) = |c|.
Proof.
  intros.
  unfold QSign, CanonicalNotations.norm,
  NormSpace_instance_Q.
  destruct (decide (a < 0)) as [Hd | Hd]; auto.
  apply Qabs.Qabs_opp.
Qed.

Lemma multMiddle: ∀ (a b c : CR),
  a*b*c = a*c*b.
Proof.
  intros.
  prepareForCRRing.
  ring.
Qed.

Open Scope Q_scope.
Lemma  Qle_shift_div_r_neg:
   ∀ a b, 0 <= a  → b < 0 → (Qdiv a  b <= 0).
Proof.
  intros. 
  unfold Qle, Qinv.
  simpl. ring_simplify.
  destruct a, b.
  unfold Qlt in H0.
  unfold Qle in H.
  simpl in H, H0.
  simpl.
  ring_simplify in H.
  ring_simplify in H0.
  unfold Qinv. simpl.
  destruct Qnum0; simpl; try omega.
  nia.
  nia.
Qed.


Close Scope Q_scope.


Lemma CRLtAddRHSConv
     : ∀ c a b : CR,  a + c < b + c -> a < b.
Proof.
  intros ? ? ? H.
  apply (CRLtAddRHS (-c)) in H.
  revert H. prepareForCRRing.
  intro H. ring_simplify in H.
  assumption.
Qed.

Lemma CRLtTrans : ∀ a b c:CR,
  a < b
  -> b < c
  -> a < c.
Proof.
  intros ? ? ? ? ? .  eapply ( orders.strict_po_trans _ _ _ );
  eauto.
Qed.

  
Lemma AddCancel : ∀ a b:CR,
  a +b -b =a.
Proof.
  intros.
  prepareForCRRing. ring.
Qed.

Hint Rewrite  <- CRopp_Qopp : MoveInjQCRIn.
Lemma polarθSignCorr1 : ∀ targetPos,
(|polarTheta targetPos|)* '(polarθSign targetPos) =polarTheta targetPos.
Proof.
  intros. unfold polarθSign, polarTheta.
  destruct (decide (X targetPos = 0)); auto.
- rewrite (mult_comm CRpi). 
  unfold CanonicalNotations.norm, NormSpace_instance_0.
  rewrite CRabs_CRmult_Q.
  rewrite CRabsCRpi.
  unfold QSignHalf.
  rewrite QAbsQSign.
  unfold CanonicalNotations.norm, NormSpace_instance_Q.
  simpl Qabs.Qabs. rewrite multMiddle.
  apply CRmult_wd;[| reflexivity].
  rewrite CRmult_Qmult.
  apply inject_Q_CR_wd.
  unfold QSign.
  destruct (decide (Y targetPos < 0)); reflexivity.
- destruct (decide (X targetPos < 0)) as [Hd | Hd].
  + unfold lt, stdlib_rationals.Q_lt, zero,
    stdlib_rationals.Q_0 in Hd, n.
    unfold QSign, CanonicalNotations.norm,
    NormSpace_instance_0.
    destruct (decide (Y targetPos < 0)) as [Hdy | Hdy].
    * rewrite CRabs_neg;[ prepareForCRRing;
      unfold stdlib_rationals.Q_1; ring|].
      apply CRweakenLt.
      apply (CRLtAddRHSConv CRpi).
      unfold π, CRpi_RealNumberPi_instance.
      prepareForCRRing.
      ring_simplify.
      rewrite <- arctan_Qarctan.
      eapply CRLtTrans;[apply CRarctan_range|].
      exists 1%nat.
      vm_compute. reflexivity.

    * rewrite CRabs_pos;[ prepareForCRRing;
      unfold stdlib_rationals.Q_1; ring|].
      apply CRweakenLt.
      apply (CRLtAddRHSConv (- CRpi)).
      unfold π, CRpi_RealNumberPi_instance.
      rewrite AddCancel.
      rewrite <- arctan_Qarctan.
      eapply CRLtTrans; [|apply (proj1 (CRarctan_range _))].
      exists 1%nat.
      vm_compute. reflexivity.

  + unfold lt, stdlib_rationals.Q_lt, zero,
    stdlib_rationals.Q_0 in Hd, n.
    unfold QSign, CanonicalNotations.norm,
    NormSpace_instance_0.
    destruct (decide (Y targetPos < 0)) as [Hdy | Hdy].
    * unfold lt, stdlib_rationals.Q_lt, zero,
      stdlib_rationals.Q_0 in Hdy.
      unfold cast. autorewrite with MoveInjQCRIn.
      rewrite CRabs_neg;[ prepareForCRRing;
        unfold stdlib_rationals.Q_1; ring|].
      apply rational_arctan_nonpos.
      prepareForLra. prepareForCRRing.
      unfold equiv, stdlib_rationals.Q_eq in n.
      apply Qle_shift_div_r; try lra.

    * unfold lt, stdlib_rationals.Q_lt, zero,
      stdlib_rationals.Q_0 in Hdy.
      rewrite CRabs_pos;[ prepareForCRRing;
        unfold stdlib_rationals.Q_1; ring|].
      apply rational_arctan_nonneg.
      prepareForLra. prepareForCRRing.
      unfold equiv, stdlib_rationals.Q_eq in n.
      apply Qle_shift_div_l; try lra.
Qed.

(** broke after making the angle more optimal s
    
Lemma Cart2PolarAngleRange : forall (c :Cart2D Q),
  -π  ≤ θ (Cart2Polar c) ≤ π.
Proof.
  intro c.
  destruct c. simpl.
  unfold polarTheta.
  simpl. destruct (decide (X = 0)).
- clear. unfold QSignHalf, QSign.
  destruct (decide (Y < 0));
  [split;[|apply CRweakenLt]|apply CRweakenRange; split];  
    try(exists (1%nat); vm_compute; reflexivity).
  rewrite <- CRopp_Qopp.
  rewrite  multNegShiftOut.
  rewrite <- CRle_opp.
  assert (π = π * 1) by ring.


 reflexivity.
- destruct (CRarctan_range ('(Y/X)%Q)) as [Hl Hr].
  destruct (decide (X < 0)); rewrite <- arctan_Qarctan.
  + apply (CRLtAddRHS π) in Hr.
    apply (CRLtAddRHS π) in Hl.
    apply CRweakenLt in Hr.
    assert (½ * π + π = (½+1)%CR*π) as Heq by CRRing.
    rewrite Heq in Hr. clear Heq.
    assert ((½ + 1) = 3*½)%Q as Heq by reflexivity.
    rewrite <- Heq. clear Heq.
    split;[apply CRweakenLt|].
    * eapply (orders.strict_po_trans); [| apply Hl].
      exists 1%nat. vm_compute. reflexivity.
    * eapply CRle_trans; [apply Hr|]. rewrite <- CRplus_Qplus.
      reflexivity.
  + apply CRweakenRange. split; [trivial|].
    eapply (orders.strict_po_trans); eauto.
    exists 1%nat. vm_compute. reflexivity.
Qed.
*)

Lemma Cart2PolarRadRange : forall (c :Cart2D Q),
  0  ≤ rad (Cart2Polar c).
Proof.
  intros c.
  unfold Cart2Polar. unfold CanonicalNotations.norm, NormSpace_instance_Cart2D.
  simpl. rewrite <- CRsqrt_Qsqrt. apply CRsqrt_nonneg.
  destruct c.
  simpl.
  apply CRle_Qle. unfoldMC. apply Q.Qplus_nonneg;apply Qpower.Qsqr_nonneg.
Qed.

