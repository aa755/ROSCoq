
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
match (decide ((X cart) = 0)) with
| yes _ => CRpi * ' QSignHalf (Y cart)
| no Hdec =>
    let angle := (rational_arctan (Y cart // (X cart ↾ Hdec))) in
    if decide (X cart < 0) then angle + CRpi else angle
end.

Definition polarRad (cart : Cart2D Q) : CR :=
  (√((X cart) * (X cart) +  (Y cart) * (Y cart)))%Q.

Definition Cart2Polar (cart :Cart2D Q) : Polar2D CR :=
  {|rad := polarRad cart 
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


(** lets first port lemmas about IR sin cos
    to a separate file and then use them separately here *)
Lemma Cart2Polar2CartID : forall (c :Cart2D Q),
  ' c = Polar2Cart (Cart2Polar c).
Proof.
  intros c.
  unfold Cart2Polar, Polar2Cart.
  simpl. destruct c as [cx cy].
  unfold polarTheta. simpl.
  destruct (decide (cx = 0)) as [Hcx0 | Hcx0];
  unfold polarRad,equiv,EquivCart; simpl.
- rewrite Hcx0. prepareForCRRing.
  QRing_simplify.
  simpl. rewrite CRrational_sqrt_ofsqr.
  unfold QSignHalf.
  destruct (decide (cy < 0)) as [Hlt | Hlt];
    autorewrite with CRSimpl; 
  prepareForCRRing; try rewrite (morph_opp QCRM);
  split; CRRing.
- destruct (decide (cx < 0)) as [HcxNeg | HcxNeg].
  + rewrite  CRCos_plus_Pi,  CRSin_plus_Pi. admit.
  + apply orders.full_pseudo_srorder_le_iff_not_lt_flip in HcxNeg.
    apply CRle_Qle in HcxNeg.
    split.
    * rewrite <- arctan_Qarctan. apply EqIfSqrEqNonNeg; trivial;
        [apply orders.nonneg_mult_compat; unfold PropHolds;
          eauto using CRrational_sqrt_nonneg, cos_o_arctan_nonneg; fail|].
Lemma sqrProdRW : forall c d : CR , d * c * (d * c) = (d*d)*(c*c).
Proof.
  intros c d. CRRing.
Qed.
Require Import  MathClasses.interfaces.additional_operations.
    rewrite sqrProdRW.
    symmetry.
    
    rewrite rings.mult_comm.
    rewrite <- CRpower_N_2. 

    rewrite  arctan_Qarctan.
    unfold recip, dec_fields.recip_dec_field, dec_recip,
      stdlib_rationals.Q_recip, mult, stdlib_rationals.Q_mult.
      simpl. idtac. fold (Qdiv cy cx).
    rewrite sqr_o_cos_o_Qarctan_o_div;[|assumption].
    



match goal with
  [|- context [√?a]] => remember (√a)%Q as d
end.
match goal with
  [|- context[cos ?x]] => remember (cos x)%Q as c
end.



    apply .

Lemma multNonNeg : forall a b,
  
      

Abort.



    

