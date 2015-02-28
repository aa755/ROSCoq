Require Export CartCR.
Require Export MCInstances.

Open Scope mc_scope.
Instance Pi_Instance_IR: RealNumberPi ℝ :=
 Pi.

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

Require Import Psatz.

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

Add Ring RisaRing: (CRing_Ring IR).
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

Instance Proper_instance_ConstTContR :
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
