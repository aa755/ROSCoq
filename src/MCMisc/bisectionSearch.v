Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import Coq.Init.Datatypes.
Section BisectionSearch.
Context {A B : Type}.
Variable  bisect : A -> A -> A.

(** the decision of  need not be exact. Indeed, it is
not exact when B is a type of constructive reals. *)
Variable compareWith0 : B -> Datatypes.comparison.

Variable f : A -> B.

Variable target : B.

(** the goal is to find an [(a:A)] such that [(f a)] is close/equal to
[target]. [f] is a non-decreasing function.*)

Let Pair (A:Type) : Type := A * A.

(**None indicates -/+ inf*)
Let SearchRange := Pair (option A).

Definition bisectStep  (s : SearchRange) : SearchRange.
Abort.

(** how many steps to take? We also need to have some kind
of a Lipschitz condition has a hypothesis  *)

End  BisectionSearch.
