Class SqrtFun (A B : Type) := sqrtFun : A -> B.
Notation "√" := sqrtFun.

Class RealNumberPi (R : Type) := π : R.

Class HalfNum (R : Type) := half_num : R.
Notation "½" := half_num.

(** Should we add other properties of distance, e.g. triangle inequality? *)
Class NormSpace (A B : Type) := norm : A -> B.
Notation "| x |" := (norm x) (at level 300).
