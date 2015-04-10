Require Export CartCR.
Require Export CartIR.


Class StrongLess (A : Type ):= strongLess : A -> A -> Type.

Notation " a ≪ b" := (strongLess a b) (at level 100).


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
  ring_strongSetoid : StrongSetoid A;
  StrongSetoidRing_plus_ext : StrongSetoid_BinaryMorphism plus;
  StrongSetoidRing_mult_ext : StrongSetoid_BinaryMorphism mult 
}.

(** make sure that A4 and A5 are provable. 
    if not, add A4 and change type of [MeasureRing_mult_ext]
    to be A5 *)

Section MeasureProps.
Context `{StrongSetoidRing A} (μ : A -> IR).

Definition MeasurePropM1 := ∀ x y,
  μ (x \p/ y) = μ x + μ y - μ (x /p\ y).

Definition MeasurePropM2 := ∀ x,
  0 ≪ (μ x) →  apart x 0 .

Definition MeasurePropM23 := ∀ x,
  0 < (μ x) <->  apart x 0 .

Class MeasureAlgebra := {
  mpm1 : MeasurePropM1;
  mpm2 : MeasurePropM23
}.

Class ProbabilityAlgebra := {
  meaurepropm1 : MeasurePropM1;
  meaurepropm23 : MeasurePropM23;
  probWholeSpace1 : μ 1 = 1
}.

End MeasureProps.

(** Lemma 1.4*)


Section Metric.

Class ProbabilityAlgebra := {
  meaurepropm1 : MeasurePropM1;
  meaurepropm23 : MeasurePropM23;
  probWholeSpace1 : μ 1 = 1
}.


