Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.

Section BisectionSearch.
Context {A B : Type}.
Variable  bisect : A -> A -> A.

(** the decision of positivity need not be exact. Indeed, it is
not exact when B is a type of constructive reals. *)
Variable posDecide : B -> bool.

Variable f : A -> B.

Variable target : B.

(** the goal is to find an [(a:A)] such that [(f a)] is close/equal to
[target]. [f] is a non-decreasing function.*)

Let SearchRange := (A * A)%type.

Definition bisectStep  (s : SearchRange) : SearchRange.
Abort.

End  BisectionSearch.
