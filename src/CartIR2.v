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

Lemma SinMinusSwap : forall a b:IR,
  sin (a - b) = - sin (b - a).
Proof using.
  intros ? ?.
  autounfold with IRMC.
  rewrite <- Sin_inv.
  apply Sin_wd.
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

Lemma PiBy2LePiMC : ½ * Pi [<=] Pi.
Proof using.
  rewrite PiBy2DesugarIR. apply less_leEq. apply HalfPi_less_Pi.
Qed.

(* Move *)
Lemma PiBy2IRCR:
CRasIR (½ * π) =  ½ * π.
Proof using.
  rewrite PiBy2DesugarIR.
  rewrite <- (IRasCRasIR_id (Pi [/]TwoNZ)).
  rewrite <- CRPiBy2Correct.
  rewrite commutativity.
  reflexivity.
Qed.


Lemma unitVDotRAsPolar :
  forall (q: Cart2D Q) (β : ℝ), ⟨'q, unitVec β ⟩ = 
  let p : Polar2D IR := 'q in
  (rad p) * cos (θ p - β).
Proof using.
  intros ? ?.
  simpl.
  rewrite CartToPolarCorrect.
  rewrite <- multDotLeft.
  rewrite unitVDot.
  reflexivity.
Qed.  


Lemma unitVDotRAsPolarNegY :
  forall (q: Cart2D Q) (β : ℝ), ⟨'(negY * q), unitVec β ⟩ = 
  let p : Polar2D IR := 'q in
  (rad p) * cos (θ p + β).
Proof using.
  intros ? ?.
  simpl.
  rewrite <- (negate_involutive β) at 2.
  rewrite <- (unitVDotRAsPolar q).
  rewrite unitVNegate.
  unfold inprod, InProductCart2D. simpl.
  do 2 rewrite preserves_mult.
  rewrite preserves_negate.
  rewrite preserves_1.
  IRring.
Qed.

Lemma unitVDotRAsPolarTranspose :
  forall (q: Cart2D Q) (β : ℝ), ⟨'(transpose q), unitVec β ⟩ = 
  let p : Polar2D IR := 'q in
  (rad p) * sin (θ p + β).
Proof using.
  intros ? ?.
  simpl.
  rewrite <- transposeCastCommute.
  rewrite (CartToPolarCorrect90Minus q).
  rewrite <- multDotLeft.
  rewrite unitVDot.
  unfold sin, SinClassIR.
  rewrite  <- Cos_HalfPi_minus.
  rewrite PiBy2DesugarIR.
  rewrite <- (@simple_associativity _ _ plus _ _).
  rewrite  negate_swap_l.
  rewrite negate_involutive.
  reflexivity.
Qed.  

Lemma unitVDotRAsPolarNflip :
  forall (q: Cart2D Q) (β : ℝ), ⟨'(nflip q), unitVec β ⟩ = 
  let p : Polar2D IR := 'q in
  (rad p) * sin (θ p - β).
Proof using.
  intros ? ?.
  simpl.
  rewrite <- unitVDotRAsPolarTranspose with (q:=q).
  rewrite unitVNegate.
  unfold inprod, InProductCart2D. simpl.
  rewrite preserves_negate.
  IRring.
Qed.

Lemma rotateAxisUnitVec: forall (θ β : IR),
  (rotateAxis β (unitVec θ))
  = unitVec (θ - β).
Proof using.
  intros ? ?.
  unfold rotateAxis.
  simpl.
  rewrite unitVDot.
  split; simpl;[reflexivity|].
  unfold inprod, InProductCart2D.
  simpl.
  symmetry.
  rewrite <- negate_mult_distr_l.
  apply Sine_minus.
Qed.

(*Move*)
Lemma halfCorrectQR : 
(½:IR)='(½:Q).
Proof using.
(*LHS was defined for nearly-arbitrary fields as 1/(1+1)*)
  unfold half_num, Q_Half_instance, cast, 
    Cast_instace_Q_IR, HalfNumIR, Half.
  change (Qmake 1 2)%Q with (1/2)%Q.
  autounfold with QMC.
  rewrite inj_Q_div.
  unfold cf_div.
  rewrite inj_Q_One.
  apply mult_wd;[reflexivity|].
  apply f_rcpcl_wd.
  setoid_rewrite inj_Q_plus.  
  rewrite inj_Q_One.
  unfold Two.
  IRring.
  
  Grab Existential Variables.
  Local Opaque inj_Q.
  simpl.
  eapply ap_wdl;[apply two_ap_zero|].
  setoid_rewrite inj_Q_plus.  
  rewrite inj_Q_One.
  unfold Two.
  IRring.
Qed.

Lemma qnormSqrIR : forall (a : Cart2D Q),
((' (| a |) * ' (| a |)):IR) = normSqr ('a).
Proof using.
  intros.
  rewrite <- normIRSpec.
  rewrite  QNormSqrIR.
  reflexivity.
Qed.

Lemma normSqrCastCommute  `{c:Cast A B} 
 `{@Ring A ae apl am az ao an}
 `{@Ring B be bp bm bz bo bn}
  `{@SemiRing_Morphism A B ae be apl am az ao bp bm bz bo c}:
  forall (a : Cart2D A),
    (' (normSqr a):B) = normSqr ('a).
Proof using.
  intros ?.
  unfold normSqr.
  rewrite preserves_plus.
  do 2 rewrite preserves_mult.
  reflexivity.
Qed.

Lemma  normIRPosAux : forall {q:Cart2D Q},
  0< normSqr q
  -> (0:IR) [<] '|q|.
Proof using.
  intros ? H.
  unfold CanonicalNotations.norm, NormSpace_instance_Cart2D.
  unfold sqrtFun, rational_sqrt_SqrtFun_instance.
  apply Qpos_adaptor in H.
  eapply less_wdr;[| symmetry; apply rational_sqrt_correct2].
  apply sqrt_less.
  eapply less_wdl;[apply H|].
  simpl. IRring.
  
  Unshelve.
  eauto 2 with CoRN.
Qed.

Lemma  normIRPos : forall {q:Cart2D Q},
  0< normSqr q
  -> (0:IR) [<] normIR ('q).
Proof using.
  intros ? H.
  apply normIRPosAux in H.
  eapply less_wdr; [apply H |].
  symmetry. apply QNormSqrIR. 
Qed.

Definition normQIRInv (q:Cart2D Q) (p: 0< normSqr q) :IR :=
normIRInv ('q) (normIRPos p).

Lemma normRatioSqr : forall (a b : Cart2D Q)  pb,
'(normSqr a / normSqr b)
  = sqr (' (| a |)  * (normQIRInv b pb)).
Proof using.
  intros ? ? ?.
  unfold sqr.
  rewrite <- MultSqrMix.
  rewrite qnormSqrIR.
  rewrite <- (@simple_associativity _ _ mult _ _).
  pose proof pb as pbb.
  apply Qpos_adaptor in pbb.
  apply less_imp_ap in pbb.
  apply ap_symmetric in pbb.
  setoid_rewrite inj_Q_div with (H:=pbb).
  rewrite <- normSqrCastCommute.
  unfold cf_div.
  apply sg_op_proper;[reflexivity|].
  unfold normQIRInv.
  apply mult_cancel_lft with (z:=(inj_Q ℝ (normSqr b)));[exact pbb|].
  rewrite field_mult_inv.
  setoid_rewrite  (@simple_associativity _ _ mult _ _).
  fold Cast_instace_Q_IR.
  fold (@cast Q IR _).
  rewrite normSqrCastCommute.
  rewrite normIRInv2.
  reflexivity.
Qed.

(*Move*)
(** countinous functions from reals to reals, 
a special case of continuous functions over an interval*)
Notation "ℝ-c->ℝ" := (IContR realline I) (at level 100).

Definition RConst (a:IR) : ℝ-c->ℝ := ContConstFun _ _ a.
Definition RFId : ℝ-c->ℝ := IContRId _ _ .

Definition linearCosine (c a b :IR) : ℝ-c->ℝ :=
RConst c [*]  (CCos [∘]  (RConst b [+]  RConst a [*] RFId )).

Definition linearSine (c a b :IR) : ℝ-c->ℝ :=
RConst c [*]  (CSine [∘]  (RConst b [+] RConst a [*] RFId  )).

Global Instance CastRInIntvl : Cast IR (@RInIntvl realline):=
fun r => {|scs_elem :=r ; scs_prf := I|}.

(* Move *)
Definition crepresents (F:(ℝ-c->ℝ)) (f: ℝ -> ℝ) : Prop :=
forall x:ℝ, {F} ('x) = f x.

Lemma linearCosineAp (c a b :IR) :
forall (θ:IR),
{linearCosine c a b} ('θ)=
let θ :IR := a*θ + b in 
c*(cos θ).
Proof using.
  intros ?. unfold
  linearCosine, RConst, RFId.
  rewrite IContRMultAp.
  rewrite composeIContAp.
  simpl.
  apply sg_op_proper;[reflexivity|].
  Local Transparent CCos Cos.
  simpl.
  unfold cos,CosClassIR, Cos.
  Local Opaque CCos Cos.
  simpl.
  apply pfwdef.
  IRring.
Qed.

(* exact same proof as [linearCosineAp ]above *)
Lemma linearSineAp (c a b :IR) :
forall (θ:IR),
{linearSine c a b} ('θ)=
let θ :IR := a*θ + b in 
c*(sin θ).
Proof using.
  intros ?. unfold
  linearSine, RConst, RFId.
  rewrite IContRMultAp.
  rewrite composeIContAp.
  simpl.
  apply sg_op_proper;[reflexivity|].
  Local Transparent CCos Cos.
  simpl.
  unfold cos,CosClassIR, Cos.
  Local Opaque CCos Cos.
  simpl.
  apply pfwdef.
  simpl. IRring.
Qed.

Lemma  composeIContRNegate :
∀ (I0 : interval) (pI : proper I0)
       (F: ℝ-c->ℝ) (G: IContR I0 pI),
        (composeIContR ([--]F) G) [=] [--] (composeIContR (F) G).
Proof using.
  intros ? ? ? ?.
  apply ExtEqIContR.
  intro a.
  rewrite composeIContAp.
  rewrite IContRInvAp.
  rewrite IContRInvAp.
  rewrite composeIContAp.
  reflexivity.
Qed.

Lemma linearCosSineDeriv (c a b :IR):
  isIDerivativeOf (linearSine (c*(-a)) a b) (linearCosine c a b).
Proof using.
  unfold linearSine, linearCosine.
  unfold RConst.
  autounfold with IRMC.
  eapply isIDerivativeOfWdl;
    [rewrite <- FConstMult; rewrite <- mult_assoc_unfolded;reflexivity|].
  apply TContRDerivativeMultConstL.
  remember (ContConstFun realline I b [+] ContConstFun realline I a [*] RFId)
  as F.
  apply (@isIDerivativeOfWdl _ _ (([--] CSine [∘] F) [*] (RConst a)) _ _);
    [|apply IContRDerivativeCos].
  - rewrite composeIContRNegate.
    rewrite cring_inv_mult_rht.
    rewrite <- cring_inv_mult_lft.
    rewrite mult_commut_unfolded.
    rewrite <-FConstOppIn.
    reflexivity.
  - subst. apply TContRDerivativeLinear.
Qed.


(* Move *)
Definition isDerivOf (f' f : IR -> IR) : Prop :=
exists (F' F : (ℝ-c->ℝ)),
crepresents F' f'
∧ crepresents F f
∧ Squash (@ContField.isIDerivativeOf realline _ F' F).


Lemma nonDecIfDerivNonNeg :forall (f' f : IR -> IR)
   (tstart tend : IR) (Hab : tstart ≤ tend),
   isDerivOf f' f
   -> (forall t:IR, (tstart ≤ t ≤ tend) -> 0 ≤ f' t)
   -> f tstart ≤ f tend.
Proof.
  intros ? ? ? ? h1 hd hn.
  destruct hd as [F' hd].
  destruct hd as [F hd].
  unfold crepresents in hd. repnd.
  do 2 rewrite <- hdrl.
  destruct hdrr.
  eapply nonDecreasingIfIDerivNonNeg; eauto.
  intros tt hb.
  specialize (hn _ hb).
  rewrite <- hdl in hn.
  eapply transitivity;[apply hn|].
  apply eq_le.
  apply TContRExt.
  simpl.
  destruct tt.
  reflexivity.
Qed.

(* Move *)
Lemma ProdImpConj : forall (A B : Prop),
A * B -> A /\ B.
Proof using.
  intros ? ? H. destruct H. auto.
Qed.

Lemma isDerivLB :forall (f' f : IR -> IR) (c: IR)
   (tstart tend : IR) (Hab : tstart ≤ tend),
   isDerivOf f' f
   -> (forall t:IR, (tstart ≤ t ≤ tend) -> c ≤ f' t)
   ->  c * (tend - tstart) ≤ f tend - f tstart.
Proof using.
  intros ? ? ? ? ? h1 hd hn.
  destruct hd as [F' hd].
  destruct hd as [F hd].
  unfold crepresents in hd. repnd.
  do 2 rewrite <- hdrl.
  destruct hdrr.
  eapply transitivity;
    [ |eapply IDerivativeLB3 with (c:=c); eauto] ;[reflexivity|].
  intros tt hb.
  apply ProdImpConj in hb.
  specialize (hn tt hb).
  rewrite <- hdl in hn.
  eapply transitivity;[apply hn|].
  apply eq_le.
  apply TContRExt.
  simpl.
  destruct tt.
  reflexivity.
Qed.

Lemma isDerivUB :forall (f' f : IR -> IR) (c: IR)
   (tstart tend : IR) (Hab : tstart ≤ tend),
   isDerivOf f' f
   -> (forall t:IR, (tstart ≤ t ≤ tend) ->  f' t ≤ c)
   ->  f tend - f tstart ≤ c * (tend - tstart).
Proof using.
  intros ? ? ? ? ? h1 hd hn.
  destruct hd as [F' hd].
  destruct hd as [F hd].
  unfold crepresents in hd. repnd.
  do 2 rewrite <- hdrl.
  destruct hdrr.
  eapply transitivity;
    [ eapply IDerivativeUB3 with (c:=c); eauto|] ;[|reflexivity].
  intros tt hb.
  apply ProdImpConj in hb.
  specialize (hn tt hb).
  rewrite <- hdl in hn.
  eapply transitivity;[|apply hn].
  apply eq_le.
  apply TContRExt.
  simpl.
  destruct tt.
  simpl.
  reflexivity.
Qed.

