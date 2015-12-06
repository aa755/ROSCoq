Class SqrtFun (A B : Type) := sqrtFun : A -> B.
Notation "√" := sqrtFun.

Class RealNumberPi (R : Type) := π : R.

Class HalfNum (R : Type) := half_num : R.
Notation "½" := half_num.

(** TODO : use the class
MathClasses.interfaces.vectorspace.Norm instead
of this class. That file also has an axiomatization
of usualy properties of norm. *)
Class NormSpace (A B : Type) := norm : A -> B.
Notation "| x |" := (norm x) (at level 300).

Class ProjectionFst (Prod A : Type) := π₁ : Prod -> A.

Instance ProjectionFst_instance_prod (A B : Type) :  
    ProjectionFst (prod A  B) A := (@fst A B) .

Instance ProjectionFst_instance_conj (A B : Prop) :  
    ProjectionFst (A /\ B) A := (@proj1 A B) .

Class Subset (A : Type)
  := subset : A -> A -> Prop.

Require Import Coq.Unicode.Utf8.
Infix "⊆" := (subset) (at level 70, no associativity): mc_scope.
Open Scope mc_scope.
Notation "x ⊆ y ⊆ z" := ((x ⊆ y) ∧ (y ⊆ z)) (at level 70, y at next level) : mc_scope.

(*
Require Export Coq.Unicode.Utf8.

Class PairType (A : Type) (P: A → Type) (T :Type) :=
{
  π₁ : T → A;
  π₂ : ∀ (t:T), P (π₁ t) 
}.

Instance PairType_instance_prod (A B : Type) :  
    PairType A (λ _, B) (prod A  B).
  constructor.
  exact (@fst A B) .
  exact (@snd A B) .
Defined.

Instance PairType_instance_conj (A B : Type) :  
    PairType A (λ _, B) ( A  B).
  constructor.
  exact (@fst A B) .
  exact (@snd A B) .
Defined.
*)