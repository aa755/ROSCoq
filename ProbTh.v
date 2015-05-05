Require Export CartCR.
Require Export CartIR.

Set Implicit Arguments.

Definition tiff (A B : Type):= (A → B) × (B → A).

Notation " A  ⇔ B" := (tiff A B) (at level 100).

Lemma RingPlusCommutative  `{Ring A} :
  forall (x y:A), x + y= y + x.
Proof.
  intros.
  apply ring_group in H.
  apply abgroup_commutative in H.
  apply H.
Qed.



Class StrongLess (A : Type ):= strongLess : A -> A -> Type.

Notation " a <ᵀ b" := (strongLess a b) (at level 100).


Instance StrongLess_instance_IR : StrongLess IR 
    := (@cof_less IR).

Instance StrongLess_instance_CR : StrongLess CR 
    := (CRltT).


(** Coqand defined much of the theory for ringish
    things that dont need to have an identity.
    However, for defining probabilities, we need it anyway.
    As we will see later, for probability, 
      1 is like the event \Omega, the
    one with probability 1.
    0 represents the "empty-set" event*)

Section BoolRing.
Variable A : CRing.

Require Export CRRing2MCRing.

Require Export MCmisc.BooleanAlgebra.




(** make sure that A4 and A5 are provable. 
    if not, add A4 and change type of [MeasureRing_mult_ext]
    to be A5 *)

Definition MeasurePropM1 
     (μ : A -> IR) : Prop := 
  ∀ x y, μ (x ∪ y) = μ x + μ y - μ (x ∩ y).

Notation "a ≷ b" := (cs_ap a b) (at level 100).

Definition MeasurePropM2 
     (μ : A -> IR) : Type := 
∀ x,   (0 <ᵀ (μ x)) →  (x ≷ 0).

Definition MeasurePropM23 
     (μ : A -> IR) : Type:=  
  ∀ x,  (0 <ᵀ(μ x)) ⇔  (x ≷ 0).

Class MeasureAlgebra  (μ : CSetoid_fun A  IR) 
  := {
  mpmboolean :>  BooleanAlgebra A;
  mpm0 : ∀ x,  0 ≤ μ x;
  mpm1 : MeasurePropM1 μ;
  mpm2 : MeasurePropM23 μ
}.


Class ProbabilityAlgebra `{H: MeasureAlgebra μ}
 :=  probWholeSpace1 : μ 1 = 1.


Section MetricSpace.
Context `{ProbabilityAlgebra μ}.
Require Export CoRN.metrics.CMetricSpaces.

(** The goal is to create an instance of [CMetricSpace]
    based on Lemma 1.4 *)


Lemma MeasurePropM1RW :
  ∀ x y, μ (x ∪ y) + μ (x ∩ y) = μ x [+] μ y .
Proof.
  intros ? ?.
  rewrite mpm1.
  admit.
Qed.

Add Ring RisaRing: (CRing_Ring IR).
Add Ring  stdlib_ring_theorylds : 
  (rings.stdlib_ring_theory A).

Definition distance : CSetoid_bin_fun A A IR :=
  compose_CSetoid_un_bin_fun ℝ A A csg_op μ.

Lemma measureMonotone : ∀ a b,
  a ⊆ b -> μ a ≤ μ b.
Proof.
  intros ? ? Hs.
  unfold setSubset in Hs.
Definition ProbAlgebraMSP : CPsMetricSpace.
  eapply Build_CPsMetricSpace with (cms_crr:=A) 
    (cms_d := distance). split.
- unfold com. intros ? ?. unfold distance.
  simpl. apply csf_wd.
  apply cag_commutes_unfolded.
- unfold nneg.
  simpl.
  intros ? ?. apply mpm0.
- unfold pos_imp_ap.
  simpl. intros  ? ? Hgt.
  apply mpm2 in Hgt.
  apply plus_cancel_ap_rht with (z:= y).
  eapply ap_wdr_unfolded;[apply Hgt|].
  symmetry.
  apply BooleanAlgebraXplusX.
- unfold tri_ineq. intros ? ? ?.
  simpl. simpl.
  assert (x + (y + y) + z = (x + y) + (y + z)) as Hr by ring.
  rewrite BooleanAlgebraXplusX in Hr.
Hint Unfold Plus_instance_TContR Plus_instance_TContR 
Zero_instance_TContR: IRMC.
  autounfold with IRMC in Hr.
(* Add Ring RisaRing1: (CRing_Ring A). *)
  rewrite  cm_rht_unit_unfolded in Hr.
  rewrite Hr.
  (** is μ monotone? if so use paperEq 1*)
  admit.

Qed.

End MetricSpace.
End BoolRing.
