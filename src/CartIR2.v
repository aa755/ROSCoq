Require Import CartCR.
Require Import MCInstances.
Require Import IRMisc.LegacyIRRing.


(**Ideally, this file should be a part of CartIR.v
However, many other old files depend on CartIR.v,
and changing it may break stuff. Eventually 
this file should be apended to it. *)

Require Import CartIR.
Require Import geometry2D.
Require Import geometry2DProps.
Require Import MathClasses.interfaces.vectorspace.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCMisc.tactics.
Hint Unfold One_instance_IR : IRMC.

Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Global Instance castPolar `{Cast A B} 
  : Cast (Polar2D A) (Polar2D B) :=
  fun c => {|rad := cast A B (rad c) ;  θ := cast A B (θ c) |}.

Global Instance cart2PolarIR : Cast (Cart2D Q) (Polar2D IR):=
fun c => '(Cart2Polar c).

Global Instance NormCart2DQ : Norm IR (Cart2D Q)
 := fun c => '(|c|).

Require Import fastReals.interface.
Require Import fastReals.misc.

Definition polar2CartIR (c:Polar2D IR) : Cart2D IR :=
  '(rad c) * (unitVec (θ c)).
  
Lemma CartToPolarCorrect : ∀ (q : Cart2D Q),
  let θ:IR := '(polarTheta q) in 
  'q  = '(∥q∥) * (unitVec θ).
Proof.
  intros ?. simpl.
  apply CartToPolarToXIR.
Qed.

Lemma CartToPolarCorrect2 : ∀ (q : Cart2D Q),
  'q  = polar2CartIR (cart2PolarIR (q)).
Proof.
  intros ?. simpl.
  apply CartToPolarToXIR.
Qed.

Lemma multDotRight : forall (a:IR) (b c : Cart2D IR),
a * (⟨b,c⟩) = ⟨('a) * c, b⟩.
Proof using.
  intros.   unfold inprod, InProductCart2D.
  simpl. IRring.
Qed.


Lemma CartToPolarCorrect90Minus : ∀ (q : Cart2D Q),
  let θ:IR := '(polarTheta q) in 
  (transpose ('q))  = '(∥q∥) * (unitVec (½ * π -θ)).
Proof using.
  intros ?. simpl.
  setoid_rewrite unitVec90Minus at 1.
  unfold transpose.
  rewrite CartToPolarCorrect.
  simpl. reflexivity.
Qed.

Lemma unitVDot : ∀ (α β:IR) ,
  ⟨unitVec α, unitVec β⟩
  = cos (α-β).
Proof.
  intros ? ?.
  unfold inprod, InProductCart2D, unitVec.
  simpl.
  symmetry.
  apply Cos_minus.
Qed.


Lemma unitVDot2 : ∀ (α β:IR) ,
  ⟨ {|X:=1;Y:=-1|} * unitVec α , unitVec β⟩
  = cos (α+β).
Proof.
  intros ? ?.
  unfold inprod, InProductCart2D, unitVec.
  simpl. autounfold with IRMC.
  rewrite  Cos_plus.
  IRring.
Qed.

(* Move *)
Lemma CosMinusSwap : forall a b:IR,
  Cos (a - b) = Cos (b - a).
Proof using.
  intros ? ?.
  rewrite <- Cos_inv.
  apply Cos_wd.
  IRring.
Qed.

Lemma Pi_minus_Sin: ∀ θ : ℝ, 
  Sin (π - θ) = (Sin θ).
Proof using.
  intros ?.
  rewrite negate_swap_r.
  autounfold with IRMC.
  rewrite  Sin_inv.
  unfold π, Pi_Instance_IR.
  fold (θ [-] Pi).
  rewrite Sin_minus_Pi.
  ring.
Qed.

Lemma Cart2DRadNNegIR : forall c:(Cart2D Q),
(0:IR) ≤ ' (| c |).
Proof using.
  intros.
  rewrite <- CRasIR0.
  apply CR_leEq_as_IR.
  apply Cart2PolarRadRange.
Qed.

Lemma inj_Q_nneg: forall q,
  (0:IR) ≤ 'q  <-> (Qle 0  q)%Q.
Proof using.
  intros. autounfold with IRMC.
  rewrite <- inj_Q_Zero.
  split.
  - apply leEq_inj_Q.
  - apply inj_Q_leEq.
Qed. 

Lemma divideBy2: forall c:IR,
  c = (½ * c) + (½ * c).
Proof using.
  intros. setoid_rewrite x_plus_x.
  unfold half_num. unfold HalfNumIR.
  setoid_rewrite mult_assoc_unfolded.
  rewrite (mult_commut_unfolded  _ Two).
  rewrite half_1. IRring.
Qed. 

Lemma CR_leEq2_as_IR: ∀ x y z: CR, (x ≤ y ≤ z) ↔ 
  (CRasIR x ≤ CRasIR y ≤ CRasIR z).
Proof using.
  intros ? ? ?. do 2 rewrite CR_leEq_as_IR.
  tauto.
Qed.

Lemma negateMinAsMax : forall (a b :IR), -min a b = max (-a) (-b).
Proof using.
  intros ? ?. unfold min, MinClassIR, max, MaxClassIR. 
  simpl. unfold MIN. setoid_rewrite negate_involutive.
  reflexivity.
Qed.

Lemma negateMaxAsMin : forall (a b :IR), -max a b = min (-a) (-b).
Proof using.
  intros ? ?. unfold min, MinClassIR, max, MaxClassIR. 
  simpl. unfold MIN. setoid_rewrite negate_involutive.
  reflexivity.
Qed.

Require Import MathClasses.interfaces.additional_operations. 

Require Import MCMisc.rings.

Lemma cosDoubleAsCos :
∀ (θ :IR) ,
  cos (2*θ) =2*(cos θ)^2 -1.
Proof using.
  intros.
  rewrite nat_pow.nat_pow_2.
  setoid_rewrite one_plus_one.
  autounfold with IRMC.
  rewrite Cos_double.
  IRring.
Qed.

Lemma cosDouble :
∀ (θ :IR) ,
  cos (2*θ) =1-2*(sin θ)^2.
Proof using.
  intros.
  rewrite nat_pow.nat_pow_2.
  autounfold with IRMC.
   unfold cos, CosClassIR.
  setoid_rewrite one_plus_one.
  rewrite Cos_double.
  remember Two.
  rewrite  <- (FFT θ).
  subst s.
  IRring.
Qed.

Lemma sinDouble :
∀ (θ :IR) ,
 sin (2*θ) =2*(sin θ)*(cos θ).
Proof using.
  intros. setoid_rewrite one_plus_one.
  apply Sin_double.
Qed. 

Lemma unitVDouble : ∀ (θ :IR) ,
  unitVec (2*θ) = {|X:=1-2*(sin θ)^2; Y:=  2*(sin θ)*(cos θ)|}.
Proof using.
  intros ?; split; simpl.
- apply cosDouble.
- apply sinDouble.
Qed.

Lemma unitVDoubleAsCos : ∀ (θ :IR) ,
  unitVec (2*θ) = {|X:=2*(cos θ)^2 -1 ; Y:=  2*(sin θ)*(cos θ)|}.
Proof using.
  intros ?; split; simpl.
- apply cosDoubleAsCos.
- apply sinDouble.
Qed.

Lemma cosAsSinRight : ∀ (θ :IR) ,
0 ≤ θ ≤ ½ * π
-> cos θ = √ (1 - ((sin θ)^2)).
Proof using.
  intros ? Hb.
  rewrite PiBy2DesugarIR in Hb.
  destruct Hb.
  erewrite <- (sqrt_to_nonneg (cos θ));
    [| apply Cos_nonneg; try assumption;
       eapply transitivity; eauto using MinusPiBy2Le0].
  apply sqrt_wd.
  rewrite nat_pow.nat_pow_2.
  rewrite AbsIR_eq_x;
    [rewrite  <- (FFT θ); IRring|].
  apply shift_leEq_minus'.
  ring_simplify.
  fold Le_instance_IR.
  fold (@le IR _).
  assert ((sin θ * sin θ) = ((sin θ) [^] 2)) as Heq by IRring.
  rewrite Heq.
  apply nexp_resp_leEq_one;[| apply Sin_leEq_One].
  apply Sin_nonneg;[assumption|].
  eapply transitivity;[apply H0|].
  pose proof HalfPi_less_Pi.
  eauto with CoRN.
  Grab Existential Variables.
  apply sqr_nonneg.
Qed.

Lemma ArcTan_nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ ArcTan x.
Proof using.
  intros ? Hl.
  rewrite <- ArcTan_zero.
  apply ArcTan_resp_leEq.
  assumption.
Qed.

(*
Lemma cos_o_arctan_east2:
  ∀ (cy cx: CR)
  (p: (λ y : CR, y ≶ 0) cx),
   cast CR IR cx = (cast CR IR (√ (cx * cx + cy * cy)))
                   * Cos (cast CR IR (arctan (cy // (cx ↾ p)))).
Proof using.
Admitted.
*)

Lemma cos_o_arctan_east2Q:
  ∀ (cy: CR) (cx:Q),
   (0 < cx)%Q
   -> cast Q IR cx = (cast CR IR (√ ('(cx * cx) + cy * cy)))
                   * Cos (cast CR IR (arctan (cy *'(/cx)))).
Proof using.
  intros.
  unfold cast, Cast_instace_Q_IR, Cart_CR_IR.
  rewrite <- CRasIRInj.
  rewrite <- cos_correct_CR.
  setoid_rewrite <- CR_mult_asIR.
  apply CRasIR_wd.
  apply cos_o_RQarctan_east.
  assumption.
Qed.


Definition IIR :Type :=
(st_car
     (cs_crr
        (csg_crr
           (cm_crr
              (cg_crr
                 (cag_crr (cr_crr (cf_crr (cof_crr (crl_crr IR)))))))))).

