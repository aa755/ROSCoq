
Require Export CoRN.reals.fast.CRtrans.
(* Require Export CoRN.reals.faster.ARbigD. *)
(* Require Export CoRN.ftc.IntegrationRules. *)

Require Export Coq.Program.Tactics.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.
Require Export IRLemmasAsCR.

Definition QSignHalf (q: Q) : Q :=
  if (decide (q < 0)) then (-½) else (½).

Require Export Vector.
Local Notation yes := left.
Local Notation no := right.

Definition polarTheta (cart :Cart2D Q) : CR :=
  if (decide ((X cart) = 0)) 
    then
      CRpi * ' QSignHalf (Y cart)
    else
      let angle := (rational_arctan (Y cart / (X cart))) in
      if decide (X cart < 0) then angle + CRpi else angle.

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
  unfold QSignHalf.
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


(* Print Assumptions Cart2Polar2CartID : Closed under the global context *)