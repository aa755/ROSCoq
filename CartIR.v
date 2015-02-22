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
Admitted.

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
