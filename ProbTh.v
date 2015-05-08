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

Definition MeasureNonZero 
     (μ : A -> IR) : Prop := ∀ x,  0 ≤ μ x.

Definition MeasurePropM23 
     (μ : A -> IR) : Type:=  
  ∀ x,  (0 <ᵀ(μ x)) ⇔  (x ≷ 0).

Class MeasureAlgebra  (μ : CSetoid_fun A  IR) 
  := {
  mpmboolean :>  BooleanAlgebra A;
  mpm0 : MeasureNonZero μ;
  mpm1 : MeasurePropM1 μ;
  mpm2 : MeasurePropM23 μ
}.

Lemma MeasurePropM23Implies2 : ∀ (μ : A → IR) ,
  MeasurePropM23 μ
  → MeasurePropM2 μ.
Proof.
  unfold MeasurePropM23, MeasurePropM2.
  intros ? X x.
  destruct (X x).
  assumption.
Qed.

Hint Resolve mpm0 mpm1 mpm2 MeasurePropM23Implies2: Alg.



Lemma MeasurePropM2Implies : ∀ (μ : A → IR) ,
  MeasurePropM2 μ
  → MeasureNonZero μ
  → μ 0 = 0.
Proof.
  intros μ Hm Hp.
  unfold MeasurePropM2 in Hp.
  apply not_ap_imp_eq.
  intro Hc.
  apply ap_imp_less in Hc.
  specialize (Hp 0).
  destruct Hc as [Hc|Hc];
    [ apply leEq_def in Hp;contradiction|].
  apply Hm in Hc.
  apply ap_irreflexive in Hc.
  contradiction.
Qed.


Class ProbabilityAlgebra `{H: MeasureAlgebra μ}
 :=  probWholeSpace1 : μ 1 = 1.

Section MetricSpace.
Context `{ProbabilityAlgebra μ}.
Require Export CoRN.metrics.CMetricSpaces.

(** The goal is to create an instance of [CMetricSpace]
    based on Lemma 1.4 *)

Add Ring  stdlib_ring_theoryldsIR : 
  (rings.stdlib_ring_theory IR).

Lemma MeasurePropM1RW :
  ∀ x y, μ (x ∪ y) + μ (x ∩ y) = μ x + μ y .
Proof.
  intros ? ?.
  rewrite mpm1.
  ring.
Qed.

Add Ring  stdlib_ring_theorylds : 
  (rings.stdlib_ring_theory A).

Definition distance : CSetoid_bin_fun A A IR :=
  compose_CSetoid_un_bin_fun ℝ A A csg_op μ.

Hint Unfold Plus_instance_TContR Mult_instance_TContR 
Zero_instance_TContR Negate_instance_TContR: IRMC.

Lemma subsetUnionMeasure : ∀ a b: A,
  a ⊆ b →  (a ∪ b) = b.
Proof.
  intros ? ? Hs.
  unfold setSubset in Hs.
  unfold setUnion, BooleanAlgUnion.
  rewrite <- Hs.
  assert (a + b + a= b + (a + a)) as Hr by ring.
  rewrite Hr. clear Hr.
  rewrite BooleanAlgebraXplusX.
  ring.
Qed.

Lemma plusAssocUnfolded `{SemiRing R}:
  ∀ (a b c : R), a + b + c = a + (b + c).
Proof.
  intros. rewrite (plus_assoc a b c).
  reflexivity.
Qed.

(** For a proof in classical measure theory,
    See page 11 of undergrad Prob. Th. course notebook*)

Lemma measureMonotone : ∀ a b : A,
  a ⊆ b → μ a ≤ μ b.
Proof.
  intros ? ? Hs.
  unfold setSubset in Hs.
  assert (b = a ∪ (b*(b+a))) as Hu.
  - unfold setUnion, BooleanAlgUnion.
    ring_simplify.
    rewrite boolean_mult.
    rewrite <- (mult_assoc b a a).
    rewrite boolean_mult.
    assert (b * a + b + b * a + b * a + a =
             a +  b + b * a + (b * a + b * a)) as Hr by ring.
    rewrite BooleanAlgebraXplusX in Hr.
    rewrite Hr.
    autounfold with IRMC.
    rewrite cm_rht_unit_unfolded.
    clear Hr. rewrite mult_commutes.
    assert (a[+]b[+]a[*]b = a ∪ b) as Hr by reflexivity.
    rewrite Hr.
    rewrite subsetUnionMeasure.
    reflexivity. exact Hs.
  - rewrite Hu.
    rewrite mpm1.
    unfold setIntersection, BooleanAlgIntersection.
    assert (a * (b * (b + a)) = a * (b * b) + a * a * b) 
      as Hr by ring; rewrite Hr; clear Hr.
    rewrite boolean_mult.
    rewrite boolean_mult.
    rewrite BooleanAlgebraXplusX.
    rewrite  MeasurePropM2Implies; auto with Alg.
    unfold negate.
    rewrite minus_0_r.
    autounfold with IRMC.
    apply addNNegLeEq.
    apply mpm0.
Qed.

Definition ProbAlgebraPsMSP : CPsMetricSpace.
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
  autounfold with IRMC in Hr.
(* Add Ring RisaRing1: (CRing_Ring A). *)
  rewrite  cm_rht_unit_unfolded in Hr.
  rewrite Hr.
  pose proof  MeasurePropM1RW as Ht.
  unfold plus, Plus_instance_TContR in Ht.
  rewrite <- Ht. clear Ht.
  rewrite  <- cm_rht_unit_unfolded.
  apply plus_resp_leEq_both;
    [| apply mpm0].
  apply measureMonotone.
  apply paperEq1.
Defined.

Definition ProbAlgebraMSP : CMetricSpace.
  eapply Build_CMetricSpace with (scms_crr:=ProbAlgebraPsMSP).
  unfold apdiag_imp_grzero.
  simpl.
  intros ? ? Hap.
  apply mpm2.
  apply op_rht_resp_ap with (z:=y) in Hap.
  eapply ap_wdr_unfolded in Hap;[exact Hap|].
  apply BooleanAlgebraXplusX.
Defined. 
  
End MetricSpace.
End BoolRing.
