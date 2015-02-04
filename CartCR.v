
Require Export CoRN.reals.fast.CRtrans.
(* Require Export CoRN.reals.faster.ARbigD. *)
(* Require Export CoRN.ftc.IntegrationRules. *)

Require Export Coq.Program.Tactics.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.
Require Export IRLemmasAsCR.

Definition QSign (q r: Q) : Q :=
  if (decide (q < 0)) then (-r) else (r).

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
      if decide (X cart < 0) then angle + π else angle.

Require Export CanonicalNotations.

Instance NormSpace_instance_Cart2D 
  (A B : Type) `{SqrtFun A B} 
  `{Ring A} : NormSpace (Cart2D A) B :=
 λ (cart : Cart2D A), 
    (√((X cart) * (X cart) +  (Y cart) * (Y cart))).


Definition Cart2Polar (cart :Cart2D Q) : Polar2D CR :=
  {|rad := ( |cart| )  
  ; θ := polarTheta cart |}.


(**
  Require Export CoRN.util.Extract.

  Time Eval vm_compute in answer 10 ((4*(polarTheta {|X:=1; Y:=1|}))).
  = 31415926535%Z
     : Z
  Finished transaction in 0. secs (0.u,0.s)

  Time Eval vm_compute in answer 10 ((4*(polarTheta {|X:=1; Y:=1|}))).
  = 31415926535%Z
     = (-31415926536)%Z
     : Z
  Finished transaction in 0. secs (0.0160000000005u,0.s)

  Time Eval vm_compute in answer 10 ((4*(polarTheta {|X:=1; Y:=1|}))).
  = 31415926535%Z
     = (-31415926536)%Z
     : Z
  Finished transaction in 0. secs (0.0160000000005u,0.s)

  Time Eval vm_compute in answer 10 
    (((polarTheta {|X:=-1; Y:=-1|})*(cast Q CR (4#5)))).
  
   = 31415926535%Z
     : Z
  Finished transaction in 0. secs (0.0150000000003u,0.s)

  Time Eval vm_compute in answer 10 
      (((polarTheta {|X:=-1; Y:=1|})*(cast Q CR (4#3)))).
     = 31415926535%Z
     : Z
  Finished transaction in 0. secs (0.0160000000005u,0.s)    
*)


Definition Polar2Cart (pol : Polar2D CR) : Cart2D CR :=
  {|X := (rad pol) * (cos (θ pol)) 
  ; Y := (rad pol) * (sin (θ pol)) |}.

Instance castCart `{Cast A B} : Cast (Cart2D A) (Cart2D B) :=
  fun c => {|X := cast A B (X c) ;  Y := cast A B (Y c) |}.

Instance EquivCart  `{Equiv A} : Equiv (Cart2D A) :=
fun ca cb => (X ca = X cb /\ Y ca = Y cb).

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
  unfold equiv,EquivCart,CanonicalNotations.norm, NormSpace_instance_Cart2D ; simpl. simpl.
- rewrite Hcx0. prepareForCRRing.
  unfold stdlib_rationals.Q_mult, stdlib_rationals.Q_plus. QRing_simplify.
  simpl. rewrite CRrational_sqrt_ofsqr.
  unfold QSignHalf, QSign.
  destruct (decide (cy < 0)) as [Hlt | Hlt];
    autorewrite with CRSimpl; 
  prepareForCRRing; try rewrite (morph_opp QCRM);
  split; CRRing.
- destruct (decide (cx < 0)) as [HcxNeg | HcxNeg].
  + rewrite  CRCos_plus_Pi,  CRSin_plus_Pi. split;
    [apply cos_o_arctan_west| apply sin_o_arctan_west]; assumption.
  + apply orders.full_pseudo_srorder_le_iff_not_lt_flip in HcxNeg.
    apply CRle_Qle in HcxNeg.
    split; [apply cos_o_arctan_east |  apply sin_o_arctan_east];
       apply CRle_Qle in HcxNeg; revert Hcx0 HcxNeg;
        unfoldMC; intros; lra.
Qed.

Require Export orders.

Hint Resolve CRweakenLt CRLtAddLHS CRLtAddRHS : CRBasics.
Lemma Cart2PolarAngleRange : forall (c :Cart2D Q),
  -(½*π)  ≤ θ (Cart2Polar c) ≤ ('(3*½))*π.
Proof.
  intro c.
  destruct c. simpl.
  unfold polarTheta.
  simpl. destruct (decide (X = 0)).
- clear. unfold QSignHalf, QSign.
  destruct (decide (Y < 0));
  [split;[|apply CRweakenLt]|apply CRweakenRange; split];  
    try(exists (1%nat); vm_compute; reflexivity).
  rewrite rings.mult_comm, <- multNegShiftOut.
  rewrite <- CRopp_Qopp. reflexivity.
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

Lemma Cart2PolarRadRange : forall (c :Cart2D Q),
  0  ≤ rad (Cart2Polar c).
Proof.
  intros c.
  unfold Cart2Polar. unfold CanonicalNotations.norm, NormSpace_instance_Cart2D.
  simpl.
Abort.