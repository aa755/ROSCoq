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

Class CommutativeRing `{Ring A} :=  
  comm_ring_mult : Commutative (@mult A _).

(** Coqand defined much of the theory for ringish
    things that dont need to have an identity.
    However, for defining probabilities, we need it anyway.
    As we will see later, for probability, 
      1 is like the event \Omega, the
    one with probability 1.
    0 represents the "empty-set" event*)

Class BooleanAlgebra `{CommutativeRing A} :=
  boolean_mult : ∀ x:A, x*x=x.

Notation "a /p\ b " := (a * b) (at level 100).
Notation "a \p/ b " := (a + b + a*b) (at level 100).

(** just le in the paper *)
Notation "x ⊑ y " := (x = x /p\ y) (at level 100).
Notation "b \ x " := (b + b * x) (at level 100).

Notation "x ᶜ  " := (1 \ x) (at level 100).

Class StrongSetoidRing `{BooleanAlgebra A} `{Apart A} := {
  ring_strongSetoid :> StrongSetoid A;
  StrongSetoidRing_plus_ext : StrongSetoid_BinaryMorphism plus;
  StrongSetoidRing_mult_ext : StrongSetoid_BinaryMorphism mult 
}.

(** make sure that A4 and A5 are provable. 
    if not, add A4 and change type of [MeasureRing_mult_ext]
    to be A5 *)

Definition MeasurePropM1 
    `{H: StrongSetoidRing A} (μ : A -> IR) : Prop := 
  ∀ x y, μ (x \p/ y) = μ x + μ y - μ (x /p\ y).

Definition MeasurePropM2 
    `{H: StrongSetoidRing A} (μ : A -> IR) : Type := 
∀ x,   (0 <ᵀ (μ x)) →  apart x 0 .

Definition MeasurePropM23 
    `{H: StrongSetoidRing A} (μ : A -> IR) : Type:=  
  ∀ x,  (0 <ᵀ(μ x)) ⇔  apart x 0 .

Class MeasureAlgebra `{H: StrongSetoidRing A} (μ : A -> IR) 
  := {
  mpm0eq :> Proper (equiv ==> (@st_eq IR)) μ;
  mpm0 : ∀ x,  0 ≤ μ x;
  mpm1 : MeasurePropM1 μ;
  mpm2 : MeasurePropM23 μ
}.



Class ProbabilityAlgebra `{H: MeasureAlgebra A μ}
 :=  probWholeSpace1 : μ 1 = 1.


Section MetricSpace.
Context `{ProbabilityAlgebra A μ}.
(** The goal is to create an instance of [MetricSpace]
    based on Lemma 1.4 *)



Definition ProbMSPSetoid : RSetoid.
  eapply Build_RSetoid with (st_car:=A).
  apply strong_setoids.Setoid_instance_0. 
Defined.

Definition distance (x y : ProbMSPSetoid) : IR := μ (x + y).

Definition PABall (e : Qpos) (a b : ProbMSPSetoid) := AbsSmall e (distance a b).

Definition ProbAlgebraMSP : MetricSpace.
  eapply Build_MetricSpace with (ball:=PABall).
- intros ? ? Hpq ? ? xeq ? ? yeq.
  unfold PABall, distance.
  rewrite xeq, yeq.
  unfold QposEq in Hpq.
  rewrite Hpq.
  tauto.
- constructor.
  + intros ? ?.
    unfold PABall, distance.
    unfold AbsSmall.
    split.
    eapply leEq_transitive;[| apply mpm0].
    

  + intros ? ? ?. unfold PABall, distance.
    rewrite RingPlusCommutative.
    tauto.
  + (*triangle *) intros. admit.
  + (*smaller ball *) intros. admit.
  + (** 0 ball *) admit.
Qed.

    






