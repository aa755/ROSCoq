Require Export CartCR.
Require Export MCInstances.

Open Scope mc_scope.

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
  Y:= ((X pt)*(Y XTowards) - (Y pt)*(X XTowards)) * (normInv) |}.

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

Definition ConstTContR (c : IR) : TContR :=
  (ContConstFun _ _ c).

Definition rotateOriginTowardsF
  (XTowards : Cart2D IR)
  (nz : 0 [<] normIR XTowards)
  (pt : Cart2D TContR) : Cart2D TContR :=
  let normInv :=  (normIRInv XTowards nz) in 
  let Xf := ConstTContR (normInv * X XTowards) in 
  let Yf := ConstTContR (normInv * Y XTowards) in 
{|X:= (Xf * X pt + Yf * Y pt);
  Y:= (Yf * X pt - Xf * Y pt)|}.

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
      × isDerivativeOf (Yf*Dx - Xf*Dy) (Y ptR)).
Proof.
  intros ? ? ? ? ?.
  simpl. intros H1d H2d.
  split.
- apply TContRDerivativePlus;
    apply TContRDerivativeMultConstL; assumption.
- apply TContRDerivativePlus;[|apply TContRDerivativeOpp];
    apply TContRDerivativeMultConstL; assumption.
Qed.

Lemma CartToPolarToXIR : ∀ (XTowards : Cart2D Q)
    (nz : 0 [<] normIR ('XTowards)),
  let normInv :=  (normIRInv ('XTowards) nz) in 
  let Xf :IR := (normInv * '(X XTowards)) in 
  let Yf :IR := (normInv * ' (Y XTowards)) in 
  let θq : IR := '(polarTheta XTowards) in 
  {|X:= Xf ; Y:=Yf|}  
    = {| X := Cos θq ; Y := Sin θq |}.
Proof.
  intros q.
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
