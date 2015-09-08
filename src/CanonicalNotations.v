Class SqrtFun (A B : Type) := sqrtFun : A -> B.
Notation "√" := sqrtFun.

Class RealNumberPi (R : Type) := π : R.

Class HalfNum (R : Type) := half_num : R.
Notation "½" := half_num.

(** Should we add other properties of distance, e.g. triangle inequality? *)
Class NormSpace (A B : Type) := norm : A -> B.
Notation "| x |" := (norm x) (at level 300).

Class ProjectionFst (Prod A : Type) := π₁ : Prod -> A.

Instance ProjectionFst_instance_prod (A B : Type) :  
    ProjectionFst (prod A  B) A := (@fst A B) .

Instance ProjectionFst_instance_conj (A B : Prop) :  
    ProjectionFst (A /\ B) A := (@proj1 A B) .



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