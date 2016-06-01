Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import Coq.Init.Datatypes.
Section BisectionSearch.
Context {A: Type}.
Variable  bisect : A -> A -> A.

(** the decision of  need not be exact. Indeed, it is
not exact in the case of constructive reals.
Lt means that the desired solution is at a lesser A.
Gt means that the desired solution is at a greater A.
Eq means this one is acceptable
*)
Variable direction : A -> Datatypes.comparison.


Let Pair (A:Type) : Type := A * A.

Let SearchRange := Pair (A).

(* either a new "shorter" search range, or that the search has terminated, optionally
with an answer.*)
Definition bisectStep  (s : SearchRange) : (SearchRange + (option A)):=
match (direction (fst s), direction (snd s)) with
(* because evaluating direction may be expensive, we consider these e special cases*)
| (Eq,_) => inr (Some (fst s))
| (_,Eq) => inr (Some (snd s))
| (Gt, Lt) => let mid := bisect (fst s) (snd s) in
    match direction mid with
    | Eq => inr (Some mid)
    | Lt => inl (fst s, mid)
    | Gt => inl (mid, snd s)
    end
| (Lt, Lt) => inr None (* solution is towards of the left of the range *)
| (Gt, Gt) => inr None (* solution is towards of the right of the range *)
| (Lt, Gt) => inr None (* a voilation of the monotonicity property *)
end.

(* fuel based search. Note that A may be a dense set, e.g. rationals. So the bisection
can go on forever *)
Fixpoint bisectionSearch  (s : SearchRange) (n:nat) :  (option A):=
match n with
| 0 => None
| S n => match bisectStep s with
        | inr r => r
        | inl s' => bisectionSearch s' n
        end
end.

End  BisectionSearch.


