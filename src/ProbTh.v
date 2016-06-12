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

Notation " a <ᵀ b" := (strongLess a b) (at level 110).


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

Require Export MCMisc.BooleanRing.


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
  mpmboolean :>  BooleanRing A;
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

Class CMeasure (T : CSetoid) := μ : CSetoid_fun T ℝ.

Class ProbabilityAlgebra `{CMeasure A}
  `{MeasureAlgebra μ}
 :=  probWholeSpace1 : μ 1 = 1.

Section MetricSpace.
Context `{ProbabilityAlgebra}.
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
    rewrite BooleanRingXplusX in Hr.
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
    rewrite BooleanRingXplusX.
    rewrite  MeasurePropM2Implies; auto with Alg.
    rewrite minus_0_r.
    autounfold with IRMC.
    apply addNNegLeEq.
    apply mpm0.
Qed.

Lemma measurePlusPropAux : ∀ x1 x2 y1 y2, 
  μ (x1+ y1 + (x2 + y2)) ≤ μ (x1 + x2) + μ (y1 + y2).
Proof.
  intros.
  rewrite <-  MeasurePropM1RW.
  rewrite  <- cm_rht_unit_unfolded.
  apply plus_resp_leEq_both;
    [| apply mpm0].
  apply measureMonotone.
  apply paperEq1.
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
  apply BooleanRingXplusX.
- unfold tri_ineq. intros ? ? ?.
  simpl. simpl.
  assert (x + (y + y) + z = (x + y) + (y + z)) as Hr by ring.
  rewrite BooleanRingXplusX in Hr.
  autounfold with IRMC in Hr.
(* Add Ring RisaRing1: (CRing_Ring A). *)
  rewrite  cm_rht_unit_unfolded in Hr.
  rewrite Hr.
  apply measurePlusPropAux.
Defined.

(** also lemma 1.4.i in the paper *)
Definition ProbAlgebraMSP : CMetricSpace.
  eapply Build_CMetricSpace with (scms_crr:=ProbAlgebraPsMSP).
  unfold apdiag_imp_grzero.
  simpl.
  intros ? ? Hap.
  apply mpm2.
  apply op_rht_resp_ap with (z:=y) in Hap.
  eapply ap_wdr_unfolded in Hap;[exact Hap|].
  apply BooleanRingXplusX.
Defined. 

Notation "a -ᵈ b" := (cms_d a b) (at level 90).

(** similar to 
    CoRN.metric2.UniformContinuity.UniformlyContinuousFunction *)

Definition uniformlyCont {X Y Z : CPsMetricSpace}
  (f : CSetoid_bin_fun X Y Z) : Type :=
∀ (eps : Qpos), {δx : Qpos | { δy :Qpos | ∀ (x1 x2 : X) (y1 y2 : Y),
      ((x1 -ᵈ x2) ≤ δx)
      → ((y1 -ᵈ y2) ≤ δy)
      → ((f x1 y1 -ᵈ f x2 y2) ≤ eps) } }.


Definition MSplus : CSetoid_bin_op ProbAlgebraMSP.
  apply csg_op.
Defined.

Definition MSmult : CSetoid_bin_op ProbAlgebraMSP.
  apply cr_mult.
Defined.

Definition qposHalf : Qpos := QposMake 1 2.

Lemma qposHalfPlus : ∀ (eps : Qpos),
  QposEq  (eps * qposHalf + eps * qposHalf)  eps.
Proof.
  intros eps.
  destruct eps.
  unfold QposEq.
  simpl.
  ring.
Qed.


Lemma qposHalfPlusQeq : ∀ (eps : Qpos),
  Qeq  (eps * qposHalf + eps * qposHalf)  eps.
Proof.
  apply qposHalfPlus.
Qed.

Require Export ROSCOQ.IRMisc.CoRNMisc.
Theorem paper1_4_ii_a_aux : uniformlyCont MSplus.
Proof.
  intros eps.
  unfold MSplus.
  simpl.
  exists (eps * qposHalf) .
  exists (eps * qposHalf) .
  intros ? ? ? ? Hx Hy.
  pose proof (plus_resp_leEq_both _ _ _ _ _ Hx Hy) as Hadd.
  clear Hx Hy.
  rewrite <- inj_Q_plus in Hadd.
  pose proof (qposHalfPlusQeq eps).
  apply (inj_Q_wd IR) in H2.
  rewrite H2 in Hadd.
  clear H2.
  eapply leEq_transitive;[|apply Hadd].
  clear Hadd.
  apply measurePlusPropAux.
Qed.
  

Theorem paper1_4_ii_b_aux : uniformlyCont MSmult.
Proof.
  intros eps.
  unfold MSmult.
  simpl.
  exists (eps * qposHalf) .
  exists (eps * qposHalf) .
  intros ? ? ? ? Hx Hy.
  pose proof (plus_resp_leEq_both _ _ _ _ _ Hx Hy) as Hadd.
  clear Hx Hy.
  rewrite <- inj_Q_plus in Hadd.
  pose proof (qposHalfPlusQeq eps).
  apply (inj_Q_wd IR) in H2.
  rewrite H2 in Hadd.
  clear H2.
  eapply leEq_transitive;[|apply Hadd].
  clear Hadd.
  pose proof  MeasurePropM1RW as Hh.
  unfold plus, Plus_instance_TContR in Hh.
  rewrite <- Hh. clear Hh.
  rewrite  <- cm_rht_unit_unfolded.
  apply plus_resp_leEq_both;
    [| apply mpm0].
  apply measureMonotone.
  apply paperEq2.
Qed.

Require Import CRMisc.OldMetricAsNew.

(* now we get access to the completion operation.
    metric2/ seems to be more developed
    than metrics/
    for efficiency, it might be better to shortcuit
   the proof of new metric space by getting
   rid of the old metric space altogether
   also, the codomain of μ can be AR or CR *)
Definition AMS : MetricSpace :=
  fromOldMetricTheory ProbAlgebraMSP.

Require Export CoRN.metric2.Complete.

Open Scope uc_scope.

(* need to redeclare the ring over AMS
Lemma Atranslate_uc_prf (a:AMS) : is_UniformlyContinuousFunction 
    (fun b:AMS => (a [+] b)) Qpos2QposInf.
Proof.
 intros e b0 b1 H.
 simpl in *.
 unfold Qball in *.
 stepr (b0-b1).
  assumption.
 simpl; ring.
Qed.

Definition Qtranslate_uc (a:AMS) : AMS --> AMS :=
Build_UniformlyContinuousFunction (Qtranslate_uc_prf a).

Definition translate (a:Q) : CR --> CR := Cmap QPrelengthSpace (Qtranslate_uc a).

Lemma translate_ident : forall x:CR, (translate 0 x==x)%CR.
Proof.
 intros x.
 unfold translate.
 assert (H:st_eq (Qtranslate_uc 0) (uc_id _)).
  intros a.
  simpl.
  ring.
 simpl.
 rewrite -> H.
 rewrite -> Cmap_fun_correct.
 apply: MonadLaw1.
Qed.

(** Lifting translate yields binary addition over CR. *)
Lemma Qplus_uc_prf :  is_UniformlyContinuousFunction Qtranslate_uc Qpos2QposInf.
Proof.
 intros e a0 a1 H b.
 simpl in *.
 repeat rewrite -> (fun x => Qplus_comm x b).
 apply Qtranslate_uc_prf.
 assumption.
Qed.

Definition Qplus_uc : Q_as_MetricSpace --> Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction Qplus_uc_prf.
Definition PlusSlow_uc : (AMS --> AMS --> AMS).
Admitted.
  

Definition PlusSlowUC : (AMSC --> AMSC --> AMSC) :=
   Cmap2_slow PlusSlow_uc.

(* general definition of a completion of a 
    metric ring? generalize the development of CR
      (e.g. [CRPlus_uc])
    Make it fast by assuming [PrelengthSpace]
      and then using [Cmap] instead of [Cmap2_slow].
    Do we need more axioms to prove that [AMS]
    is a prelengthspace?
*)
*)


Require Export CoRN.metric2.Compact.

Definition MetricallyComplete : CProp := 
  CompleteSubset AMS (λ x, True).

Definition AMSC : MetricSpace := Complete AMS.

End MetricSpace.
End BoolRing.

(*An (isometric) embedding f between measure rings (A, µ) and (B, ν) is a ring
homomorphism which is measure preserving, i.e. *)

Require Export CoRN.algebra.CRing_Homomorphisms.
Definition MeasurePreserving
  {A B : CSetoid} `{CMeasure A} `{CMeasure B}
  (f : A -> B) :=
  ∀ x,  μ (f x) = μ x.

Record IsometricProbEmbedding
  (A B : CRing) `{CMeasure A} `{CMeasure B} 
    :=  mkIsometricProbEmbedding 
{
  fIsoProbEmb :> RingHom A B;
  fMeassurePres : MeasurePreserving fIsoProbEmb
}.

