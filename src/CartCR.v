
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

Lemma  Qle_shift_div_l_neg:
   ∀ a b, a <= 0  → b < 0 → (0 <= Qdiv a  b).
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

Lemma addRangeLe : ∀ a t b v : CR, 
  (a - v) ≤ t  ≤ (b - v) → a ≤ t + v ≤ b.
Proof.
  intros ? ? ? ? Hb.
  repnd.
  split.
- apply shift_leEq_plus. assumption.
- apply shift_plus_leEq. assumption.
Qed.


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
  apply CRweakenLt.
  exists 1%nat.
  vm_compute.
  reflexivity.

- destruct (CRarctan_range ('(Y/X)%Q)) as [Hl Hr].
  rewrite arctan_Qarctan in Hl.
  rewrite arctan_Qarctan in Hr.
  destruct (decide (X < 0)) as [l|l].
  + apply addRangeLe.
    autounfold with QMC in l.
    unfold QSign, CanonicalNotations.norm,
      NormSpace_instance_0.
    destruct (decide (Y < 0)) as [Hdy | Hdy];
      autounfold with QMC in Hdy.
    * split; [
        | apply CRweakenLt;
          eapply (orders.strict_po_trans); eauto;
          exists 1%nat; vm_compute; reflexivity].
      prepareForCRRing.
      rewrite CRplus_opp.
      apply rational_arctan_nonneg.
      autounfold  with QMC.
      apply Qle_shift_div_l_neg; try lra.
    
    * split; [
          apply CRweakenLt;
          eapply (orders.strict_po_trans); eauto;
          exists 1%nat; vm_compute; reflexivity| ].
      prepareForCRRing.
      rewrite CRplus_opp.
      apply rational_arctan_nonpos.
      autounfold  with QMC.
      apply Qle_shift_div_r_neg; try lra.

  + apply CRweakenRange. split;
    eapply (orders.strict_po_trans); eauto;
    exists 1%nat; vm_compute; reflexivity.
Qed.

Lemma polarFirstQuad : forall (c: Cart2D Q),
  0 ≤ c -> 0 ≤ polarTheta c ≤ ('½)*π.
Proof.
  intros ?. unfold polarTheta, QSignHalf, QSign,
  Zero_instance_Cart2D, Cart2D_instance_le.
  autounfold with QMC.
  simpl.
  intro Hh. destruct Hh.
  destruct (decide (X c == 0)%Q).
  - simpl. destruct (decide (Y c < 0)%Q);[lra|].
    rewrite commutativity.
    split;[| reflexivity].
    apply CRweakenLt.
    exists (1%nat); vm_compute; reflexivity.
  - destruct (decide (X c < 0)%Q);[lra|].
    assert ((0 < X c)%Q) by lra.
    clear n n0.
    split.
    + apply rational_arctan_nonneg.
      autounfold  with QMC.
      apply Q.Qle_shift_div_l; lra.
    + destruct (CRarctan_range ('(Y c/X c)%Q)) as [Hl Hr].
      clear Hl.
      rewrite arctan_Qarctan in Hr.
      apply CRweakenLt.
      exact Hr.
Qed.


Lemma polarFirstQuadIncreasing : forall (a b: Cart2D Q),
  0 < X a (* if 0, LHS is arbitrarily chosen to be Pi*)
  → 0 < X b
  → (Y a / X a ≤ Y b / X b)%Q
  → polarTheta a ≤ polarTheta b.
Proof.
  intros ? ?. unfold polarTheta, QSignHalf,
    QSign,
  Zero_instance_Cart2D, Cart2D_instance_le.
  autounfold with QMC.
  simpl.
  intros ? Hlt Hrle.
  destruct (decide (X a == 0)%Q);[lra|].
  destruct (decide (X a < 0)%Q);[lra|].
  assert ((0 < X a)%Q) by lra.
  destruct (decide (X b == 0)%Q);[lra|].
  assert ((0 < X b)%Q) by lra.
  destruct (decide (X b < 0)%Q);[lra|].
  apply rational_arctan_increasing.
  exact Hrle.
Qed.

Lemma polarFirstQuadIncreasingStrict : forall (a b: Cart2D Q),
  0 < X a (* if 0, LHS is arbitrarily chosen to be Pi*)
  → 0 < X b
  → (Y a / X a < Y b / X b)%Q
  → polarTheta a < polarTheta b.
Proof using.
  intros ? ?. unfold polarTheta, QSignHalf,
    QSign,
  Zero_instance_Cart2D, Cart2D_instance_le.
  autounfold with QMC.
  simpl.
  intros ? Hlt Hrle.
  destruct (decide (X a == 0)%Q);[lra|].
  destruct (decide (X a < 0)%Q);[lra|].
  assert ((0 < X a)%Q) by lra.
  destruct (decide (X b == 0)%Q);[lra|].
  assert ((0 < X b)%Q) by lra.
  destruct (decide (X b < 0)%Q);[lra|].
  apply CR_lt_ltT.
  apply rational_arctan_increasing_strict.
  exact Hrle.
Qed.
