Class SetUnion (A : Type)
  := setUnion : A -> A -> A.

Class SetIntersection (A : Type)
  := setIntersection : A -> A -> A.

Infix "∪" := setUnion (at level 65).
Infix "∩" := setIntersection (at level 60).

Require Export MathClasses.interfaces.abstract_algebra.
Require Export MathClasses.interfaces.canonical_names.

Section SetLikeTh.
Context  `{SetUnion A} `{SetIntersection A} `{Equiv A}.

Definition setSubset (a b : A) : Prop := a = (a ∩ b). 
(** is this being to specific? Can make it arbitrary, 
  just like union *)

End SetLikeTh.
Infix "⊆" := setSubset (at level 70).
