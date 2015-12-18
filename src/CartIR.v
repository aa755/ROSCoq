Require Export CartCR.
Require Export MCInstances.
Require Import IRMisc.LegacyIRRing.

Open Scope mc_scope.

Lemma PiBy2NoMC :
   ('½) * π = Pi [/]TwoNZ.
Proof.
  apply (injective IRasCR).
  rewrite <- CRPiBy2Correct.
  unfold mult, Mult_instance_IR.
  autorewrite with IRtoCR.
  unfold cast, Cart_CR_IR.
  rewrite CRasIRasCR_id.
  pose proof (@rings.mult_comm CR _ _ _ _ _ _ ) as Hc.
  unfold Commutative in Hc.
  unfold mult in Hc.
  rewrite Hc. reflexivity.
Qed.


(** The 2D vector pointing in the direction of θ.*)
Definition unitVec (θ:IR) : Cart2D IR := {|X:= Cos θ; Y:= Sin θ|}.

Ltac IRring := autounfold with IRMC; unfold cg_minus; try ring;
                simpl; ring.

Lemma leftShiftEqIR : forall (a b c : IR),
  a [=] b [+] c <-> a [-] b [=] c.
Proof.
  intros; split ; intro H.
  - rewrite H. IRring.
  - rewrite <- H. IRring.
Qed.

  
Lemma unitVecLemma1 : forall θs θw, (unitVec (θs + θw) - sameXY (Cos θw) * unitVec θs)
  = (sameXY (Sin  θw)) * unitVec (θs + Pi [/]TwoNZ).
Proof.
  intros ? ?.
  unfold sameXY, unitVec.   autounfold with IRMC.
  rewrite Sin_plus_HalfPi.
  rewrite Cos_plus_HalfPi.
  Local Opaque Sin Cos.
  simpl. split; simpl; autounfold with IRMC;
  [rewrite Cos_plus | rewrite Sin_plus]; try IRring.
Qed.


  

  Global Instance unitVecProper : Proper (equiv ==> equiv) unitVec. 
     intros ? ? H.  unfold unitVec. rewrite H. reflexivity.
  Qed. 

Lemma cgminus_Qminus : forall (a b : Q),
  (a-b) ≡ a[-]b.
  reflexivity.
Qed.

Require Import Psatz.


Lemma QabsQpos : ∀ (qp: Qpos),
   ((Qabs.Qabs qp) == qp)%Q.
  intros.
  destruct qp; simpl.
  rewrite Qabs.Qabs_pos; lra.
Qed.

Hint Rewrite QabsQpos : CoRN.

Lemma QAbsMultSign: forall (a : Q) (b : Qpos),
  ((Qabs.Qabs a) * / b * ((QSign a 1) * b) == a)%Q.
Proof.
  intros ? ?.
  unfold QSign. destruct b as [b bp].
  simpl.
  destruct (decide (a < 0)) as [Hd | Hd]; revert Hd; unfoldMC; intro Hd.
- ring_simplify. rewrite Qabs.Qabs_neg;[|lra]. field. lra.
- ring_simplify. rewrite Qabs.Qabs_pos;[|lra]. field. lra.
Qed.


Lemma approximateAbsSmallIR: ∀ (r:CR) (eps : Qpos),
    AbsSmall eps (CRasIR r [-] (approximate r eps)).
  intros ? ?.
  pose proof (ball_approx_r r eps ) as Hball.
  apply CRAbsSmall_ball in Hball.
  fold (inject_Q_CR) in Hball.
  apply CR_AbsSmall_as_IR in Hball.
  rewrite CR_minus_asIR2 in Hball.
  rewrite <- IR_inj_Q_as_CR in Hball.
  rewrite <- IR_inj_Q_as_CR in Hball.
  rewrite IRasCRasIR_id in Hball.
  rewrite IRasCRasIR_id in Hball.
  exact Hball.
Qed.


Lemma multRAbsSmallIR:
  ∀  (y x e : IR),
  AbsSmall e x → AbsSmall (e[*]AbsIR y) (x[*]y).
Proof.
  intros.
  apply mult_AbsSmall;[assumption|].
  apply AbsIR_imp_AbsSmall.
  apply leEq_reflexive.
Qed.



Require Export Coq.QArith.Qabs.

Lemma QMinusShiftRLe:
  ∀ a b c,
  ((a - b) <= c
  -> a <= c +b)%Q.
Proof.
  intros.
  lra.
Qed.
Lemma QposDivLe0 : ∀ (qp : Qpos),
0[<=](/ qp)%Q.
Proof.
  intros.
  destruct qp.
  simpl. apply Qinv_le_0_compat.
  lra.
Qed.

Lemma QposDivLe0IR : ∀ (qp : Qpos),
[0][<=]Q2R (/ qp)%Q.
Proof.
  intros.
  apply injQ_nonneg.
  apply QposDivLe0.
Qed.

Lemma QDivQopp : forall (a b: Q),
  (-(a /b )== ((-a )/ b))%Q.
Proof.
  intros.
  destruct (decide (b=0)) as [Hd|Hd].
- rewrite Hd. destruct a.
  unfoldMC. unfold Qdiv, Qinv. simpl.
  ring.
- field. assumption.
Qed.

Lemma AbsIRQpos : ∀ (qp : Qpos),
  AbsIR qp [=] qp.
Proof.
  intros. 
  rewrite AbsIR_eq_x;[reflexivity|].
  rewrite <- inj_Q_Zero.
  apply inj_Q_leEq.
  simpl.
  destruct qp. simpl.
  lra.
Qed.

Hint Unfold Zero_instance_IR : IRMC.
Lemma Sin_nonpos
     : ∀ θ : ℝ, -π ≤ θ ≤ 0 -> Sin θ ≤ 0.
Proof.
  intros ? Hd.
  apply inv_cancel_leEq.
  autounfold with IRMC.
  autorewrite with CoRN.
  rewrite <- Sin_inv.
  repnd.
  apply inv_resp_leEq in Hdr.
  apply inv_resp_leEq in Hdl.
  autounfold with IRMC in Hdl, Hdr.
  autorewrite with CoRN in Hdr, Hdl.
  apply Sin_nonneg; assumption.
Qed.


(** This proof can be generalized for even functions.
    Similarly, [AbsIRSin] can be generalized for odd functions *)
Lemma CosEven2 : ∀ θ, 
  AbsIR θ ≤ Pi [/]TwoNZ
  -> Cos θ = Cos (AbsIR θ).
Proof.
  intros ? H.
  pose proof (leEq_or_leEq _ θ [0]) as Hd.
  apply not_ap_imp_eq.
  intro Hc.
  apply Hd.
  clear Hd. intro Hd.
  apply ap_tight in Hc;[contradiction|].
  repnd.
  destruct Hd as [c|].
- rewrite AbsIR_eq_inv_x;[|assumption].
  rewrite Cos_inv. reflexivity.
- rewrite AbsIR_eq_x; [|assumption].
  reflexivity.
Qed.

Lemma AbsIRCos : ∀ θ, 
  AbsIR θ ≤ Pi [/]TwoNZ
  -> AbsIR (Cos θ) = Cos (AbsIR θ).
Proof.
  intros ? Hb.
  rewrite <- CosEven2 by assumption.
  apply AbsIR_imp_AbsSmall in Hb.
  unfold AbsSmall in Hb.
  repnd.
  eapply Cos_nonneg in Hbl; eauto.
  rewrite AbsIR_eq_x;[| assumption].
  reflexivity.
Qed.

Lemma Cos_nonnegAbs
  : ∀ θ : ℝ, AbsIR θ [<=] Pi [/]TwoNZ → [0] [<=]Cos θ.
Proof.
  intros ? H.
  apply AbsIR_imp_AbsSmall in H.
  destruct H.
  apply Cos_nonneg; assumption.
Qed.
  


Lemma TimeRangeShortenL :
  ∀ (a b t : Q) (qt : QTime),
    a + qt ≤ t ≤ b
    -> a ≤ t ≤ b.
Proof.
  unfoldMC.
  intros ? ? ? ? Hb.
  destruct qt as [? p].
  simpl. pose proof p as pb.
  apply QTimeD in pb.
  repnd. simpl in Hbl. split; lra.
Qed.

Lemma AbsIRSine : ∀ θ, 
  -π ≤ θ ≤ π
  -> AbsIR (Sin θ) = Sin (AbsIR θ).
Proof.
  intros ? Hb.
  pose proof (leEq_or_leEq _ θ [0]) as Hd.
  apply not_ap_imp_eq.
  intro Hc.
  apply Hd.
  clear Hd. intro Hd.
  apply ap_tight in Hc;[contradiction|].
  repnd.
  destruct Hd as [c|].
- unfold CanonicalNotations.norm, NormSpace_instance_IR. 
  symmetry. rewrite AbsIR_eq_inv_x; [|assumption].
  rewrite Sin_inv.
  rewrite AbsIR_eq_inv_x; [reflexivity|].
  apply Sin_nonpos; split; try assumption.
- unfold CanonicalNotations.norm, NormSpace_instance_IR. 
  symmetry. rewrite AbsIR_eq_x; [|assumption].
  rewrite AbsIR_eq_x; [reflexivity|].
  apply Sin_nonneg; assumption.
Qed.

Definition normIR (pt : Cart2D IR) : IR.
  apply sqrt with (x:=normSqr pt).
  unfold normSqr.
  unfoldMC. unfold Plus_instance_IR, Mult_instance_IR.
  rewrite <- nexp_two.
  rewrite <- nexp_two.
  apply cc_abs_aid.
Defined.

Lemma normIRSpec : ∀ (pt : Cart2D IR), 
  (normIR pt) * (normIR pt) = (normSqr pt).
Proof.
  intros. unfoldMC. unfold Plus_instance_IR, Mult_instance_IR.
  rewrite <- nexp_two.
  apply sqrt_sqr.
Qed.

Definition normIRInv (pt : Cart2D IR) (nz : 0 [<] normIR pt) : IR.
  apply f_rcpcl with (x:= normIR pt).
  simpl. apply ap_symmetric.
  apply less_imp_ap.
  exact nz.
Defined.

Lemma normIRInvSpec : ∀ (pt : Cart2D IR)  (nz : 0 [<] normIR pt), 
   (normIR pt) * (normIRInv pt nz) = 1.
  intros. unfold normIRInv. 
  unfoldMC. unfold Plus_instance_IR, Mult_instance_IR, Zero_instance_IR,
    Negate_instance_IR.
  rewrite field_mult_inv.
  reflexivity.
Qed.

Lemma normIRInvSpecInvLeft : ∀ (pt : Cart2D IR)  (nz : 0 [<] normIR pt), 
    (normIRInv pt nz) * (normIR pt) = 1.
  
  intros. rewrite mult_comm.
  apply normIRInvSpec.
Qed.

Lemma MultIRSqrMix: 
∀ a b : IR, 
 (a * a * b * b = (a * b) * (a * b)).
  intros. 
   unfoldMC. unfold Plus_instance_IR, Mult_instance_IR, Zero_instance_IR,
    Negate_instance_IR.
  ring.
Qed.

Lemma normIRInv2 : ∀ (pt : Cart2D IR)  (nz : 0 [<] normIR pt), 
   (normSqr pt) * (normIRInv pt nz) * (normIRInv pt nz) = 1.
  intros. rewrite <- normIRSpec.
  rewrite MultIRSqrMix.
  rewrite normIRInvSpec.

  unfoldMC. unfold Plus_instance_IR, Mult_instance_IR, Zero_instance_IR,
    Negate_instance_IR, One_instance_IR.
    ring.
Qed.

(** rotate the axis so that the X axis points
    towards xAxisDir*)
Definition rotateOriginTowards 
  (XTowards : Cart2D IR)
  (nz : 0 [<] normIR XTowards)
  (pt : Cart2D IR) : Cart2D IR :=
  let normInv := normIRInv XTowards nz in 
{|X:= ((X pt)*(X XTowards) + (Y pt)*(Y XTowards)) * (normInv);
  Y:= ((Y pt)*(X XTowards) - (X pt)*(Y XTowards)) * (normInv) |}.

Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Require Import IRMisc.LegacyIRRing.
Lemma rotateOriginTowardsTowards : ∀ (XTowards : Cart2D IR)
  (nz : 0 [<] normIR XTowards),
  rotateOriginTowards XTowards nz XTowards 
  = {|X:= normIR XTowards; Y:=0|}.
Proof.
  intros. unfold rotateOriginTowards.
  unfold equiv, EquivCart.
  simpl.
  fold (normSqr XTowards).
  rewrite <- normIRSpec.
  unfoldMC. unfold Plus_instance_IR, Mult_instance_IR, Zero_instance_IR,
    Negate_instance_IR.
  split; [| ring].
  rewrite <- CRings.mult_assoc.
  unfold normIRInv. rewrite field_mult_inv.
  ring.
Qed.

Lemma rotateOriginTowardsNormSqrPreserved 
    : ∀ (XTowards : Cart2D IR)
  (nz : 0 [<] normIR XTowards) pt,
  normSqr (rotateOriginTowards XTowards nz pt)
  = normSqr pt.
Proof.
  intros. unfold rotateOriginTowards.
  unfold normSqr. simpl.
  unfoldMC. unfold Plus_instance_IR, Mult_instance_IR, Zero_instance_IR,
    Negate_instance_IR.
  match goal with
  [ |-_  [=] ?r] => assert (r [=] r [*] [1]) as Heq by ring
  end.
  ring_simplify.
  rewrite <- normIRInv2 with (nz:=nz) in Heq.
  unfold normSqr in Heq.
  rewrite Heq.
  unfoldMC. unfold Plus_instance_IR, Mult_instance_IR, Zero_instance_IR,
    Negate_instance_IR.
  ring.
Qed.

Definition ConstTContR :=
  (ContConstFun (closel [0]) I).

Global Instance Proper_instance_ConstTContR :
  Proper (@st_eq IR  ==> @st_eq TContR) ConstTContR.
Proof.
  intros ? ? Heq ?.
  simpl. assumption.
Qed.

Definition rotateOriginTowardsF
  (XTowards : Cart2D IR)
  (nz : 0 [<] normIR XTowards)
  (pt : Cart2D TContR) : Cart2D TContR :=
  let normInv :=  (normIRInv XTowards nz) in 
  let Xf := ConstTContR (normInv * X XTowards) in 
  let Yf := ConstTContR (normInv * Y XTowards) in 
{|X:= (Xf * X pt + Yf * Y pt);
  Y:= (Xf * Y pt - Yf * X pt)|}.

Definition CartFunEta (ptf : Cart2D TContR) (t:Time) : Cart2D IR :=
{|X:= {X ptf} t ; Y:= {Y ptf} t|}.


Definition XYAbs (pt : Cart2D IR) : Cart2D IR :=
{| X:= AbsIR (X pt) ; Y:= AbsIR (Y pt)|}.

Lemma Cart2D_instance_le_IRtransitive : ∀
  (a b c : Cart2D IR),
  a ≤ b
  → b ≤ c
  → a ≤ c.
Proof.
  intros ? ? ?  H1 H2.
  destruct H1, H2.
  split; eapply leEq_transitive; eauto.
Qed.

Local Opaque AbsIR.
Global Instance  : 
  Proper (equiv ==> equiv ) XYAbs.
  intros a b Heq.
  split; simpl; rewrite Heq; auto.
Qed.


Require Import MathClasses.interfaces.canonical_names.


Lemma XYAbsLeAdd :
  ∀ a b c d,
    XYAbs a ≤ c
    -> XYAbs b ≤ d
    -> XYAbs (a+b) ≤ (c+d).
Proof.
  intros ? ? ? ? H1 H2.
  destruct H1 as [H1x H1y].
  destruct H2 as [H2x H2y].
  simpl in H1x, H1y, H2x, H2y.
  split; simpl;
  apply AbsIR_plus; assumption.
Qed.

Lemma QPQTQplusnNeg: ∀ sp qt,
   (0<=(Qplus (QposAsQ sp) (QT2Q qt)))%Q.
Proof.
  intros.
  destruct sp.
  destruct qt as [? y].
  simpl.
  apply QTimeD in y.
  lra.
Qed.

Lemma rotateOriginTowardsFAp : ∀
  (XTowards : Cart2D IR)
  (nz : 0 [<] normIR XTowards)
  (pt : Cart2D TContR) (t : Time),
CartFunEta (rotateOriginTowardsF XTowards nz pt) t
= rotateOriginTowards XTowards nz (CartFunEta pt t).
Proof.
  intros ? ? ? ?.
  unfold CartFunEta, rotateOriginTowardsF.
  simpl. autorewrite with IContRApDown.
  unfold rotateOriginTowards.
  simpl. unfold equiv, EquivCart. simpl.
  unfoldMC. autounfold with IRMC.
  simpl. unfold getF. simpl.
  split; ring.
Qed.

Lemma DerivativerotateOriginTowards :
  ∀ (XTowards : Cart2D IR)
  (nz : 0 [<] normIR XTowards)
  (pt : Cart2D TContR) (Dx Dy : TContR),
  let normInv :=  (normIRInv XTowards nz) in 
  let Xf := ConstTContR (normInv * X XTowards) in 
  let Yf := ConstTContR (normInv * Y XTowards) in 
  let ptR := rotateOriginTowardsF XTowards nz pt in 
  isDerivativeOf Dx (X pt)
  → isDerivativeOf Dy (Y pt)
  → (isDerivativeOf (Xf*Dx + Yf*Dy) (X ptR)
      × isDerivativeOf (Xf*Dy - Yf*Dx) (Y ptR)).
Proof.
  intros ? ? ? ? ?.
  simpl. intros H1d H2d.
  split.
- apply TContRDerivativePlus;
    apply TContRDerivativeMultConstL; assumption.
- apply TContRDerivativePlus;[|apply TContRDerivativeOpp];
    apply TContRDerivativeMultConstL; assumption.
Qed.

Local Opaque Sin Cos.
Lemma CartToPolarToXIR : ∀ (q : Cart2D Q),
  let θq : IR := '(polarTheta q) in 
  ' q  = {| X := ('|q|) * Cos θq ; Y := ('|q|) * Sin θq |}.
Proof.
  intros ?.
  simpl.
  pose proof (Cart2Polar2CartID q) as Hid.
  unfold cast, castCart, Cast_instace_Q_IR, Cart_CR_IR.
  unfold cast, castCart, Cast_instace_Q_IR in Hid.
  unfold Polar2Cart, Cart2Polar in Hid.
  simpl in Hid.
  unfold equiv, EquivCart in Hid.
  unfold equiv, EquivCart.
  simpl in Hid. simpl.
  unfold cast.
  repnd.
  apply CRasIR_wd in Hidr.
  apply CRasIR_wd in Hidl.
  rewrite CR_mult_asIR in Hidl, Hidr.
  rewrite sin_correct_CR in Hidr.
  rewrite cos_correct_CR in Hidl.
  rewrite <- Hidl, <- Hidr.
  rewrite <- IR_inj_Q_as_CR, <- IR_inj_Q_as_CR.
  rewrite IRasCRasIR_id, IRasCRasIR_id.
  split; reflexivity.
Qed.


Lemma QNormSqrIR : ∀ (q : Cart2D Q),
  normIR ('q) = '|q|.
Proof.
  intros.
  unfold CanonicalNotations.norm, NormSpace_instance_Cart2D, sqrtFun,
    rational_sqrt_SqrtFun_instance.
  rewrite rational_sqrt_correct.
  unfold cast.
  rewrite IRasCRasIR_id.
  apply sqrt_wd.
  unfold castCart, normSqr.
Local Opaque inj_Q.
  simpl.
  unfoldMC.
  unfold Mult_instance_IR,Mult_instance_IR.
  autorewrite with InjQDown.
  reflexivity.
Grab Existential Variables.
  pose proof (cc_abs_aid _ (X q) (Y q)) as HH.
  simpl in HH.
  rewrite <- inj_Q_Zero.
  apply inj_Q_leEq.
  unfoldMC.
  simpl. simpl in HH.
  lra.
Qed.


Lemma RingLeftMult : ∀ `{Ring R} (c a b : R),
  a = b
  -> c * a = c * b.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? H.
  rewrite H.
  reflexivity.
Qed.

Lemma CartToPolarToXIR2 : ∀ (XTowards : Cart2D Q)
    (nz : 0 [<] normIR ('XTowards)),
  let normInv :=  (normIRInv ('XTowards) nz) in 
  let Xf :IR := (normInv * '(X XTowards)) in 
  let Yf :IR := (normInv * ' (Y XTowards)) in 
  let θq : IR := '(polarTheta XTowards) in 
  {|X:= Xf ; Y:=Yf|}  
    = {| X := Cos θq ; Y := Sin θq |}.
Proof.
  intros q ?.
  simpl.
  pose proof (CartToPolarToXIR q) as Hid.
  unfold equiv, EquivCart. simpl.
  unfold equiv, EquivCart in Hid.
  simpl in Hid.
  rewrite <- QNormSqrIR in Hid.
  repnd.
  apply (RingLeftMult (normIRInv (' q) nz)) in Hidr.
  apply (RingLeftMult (normIRInv (' q) nz)) in Hidl.
  rewrite sr_mult_associative in Hidr.
  rewrite sr_mult_associative in Hidl.
  rewrite normIRInvSpecInvLeft in Hidl.
  rewrite normIRInvSpecInvLeft in Hidr.
  rewrite mult_1_l in Hidl.
  rewrite mult_1_l in Hidr.
  rewrite <- Hidl, <- Hidr.
  split; reflexivity.
Qed.


Add Ring TContRisaRing: (CRing_Ring TContR).

Lemma DerivativerotateOriginTowards2 :
  ∀ (XTowards : Cart2D Q)
  (nz : 0 [<] normIR (' XTowards))
  (pt : Cart2D TContR) (V θ : TContR),
  let θt : TContR := ConstTContR ('(polarTheta XTowards)) in 
  let ptR := rotateOriginTowardsF (' XTowards) nz pt in 
  isDerivativeOf (V * (CFCos θ)) (X pt)
  → isDerivativeOf (V * (CFSine θ)) (Y pt)
  → (isDerivativeOf (V * (CFCos (θ - θt))) (X ptR)
      × isDerivativeOf (V * (CFSine (θ - θt))) (Y ptR)).
Proof.
  intros ? ? ? ? ?.
  simpl. intros H1d H2d.
  pose proof (DerivativerotateOriginTowards _ nz pt _ _ H1d H2d) as Hd.
  clear H1d H2d.
  pose proof (CartToPolarToXIR2 _ nz) as Hn.
  simpl in Hn.
  unfold equiv, EquivCart in Hn.
  simpl in Hn.
  repnd. destruct Hd as [Hdl Hdr].
  eapply isIDerivativeOfWdl in Hdr;
  [| rewrite Hnl; rewrite Hnr;reflexivity].
  eapply isIDerivativeOfWdl in Hdl;
  [| rewrite Hnl; rewrite Hnr;reflexivity].
  unfold rotateOriginTowardsF in Hdl, Hdr.
  simpl in Hdl, Hdr.
  unfold isDerivativeOf. unfoldMC.
  unfold Mult_instance_TContR, Plus_instance_TContR, Negate_instance_TContR,
    Negate_instance_TContR,Negate_instance_TContR, Mult_instance_IR.
  split.
- eapply isIDerivativeOfWdl;[| apply Hdl]. 
  pose proof  CFCos_minus as Hc.
  unfold cg_minus in Hc.
  rewrite Hc.

Local Opaque Sine Cos Cosine.
  rewrite CFCosConst, CFCosSine.
  fold ConstTContR.
  unfoldMC. unfold Plus_instance_TContR, Mult_instance_TContR.
  unfold cast. 
  fold TContR.
  ring.

- clear Hdl. eapply isIDerivativeOfWdl;[| apply Hdr].
  pose proof  CFSine_minus as Hc.
  unfold cg_minus in Hc.
  rewrite Hc. clear Hc.
  rewrite CFCosConst, CFCosSine.
  fold ConstTContR.
  unfoldMC. unfold Plus_instance_TContR, Mult_instance_TContR, 
    Negate_instance_TContR.
  unfold cast. 
  fold TContR.
  ring.
Qed.

  Require Import CoRN.logic.Stability.


Definition Cart2DIRRing := 
  (rings.stdlib_ring_theory (Cart2D IR)).
