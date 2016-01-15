
Require Import MathClasses.interfaces.canonical_names.

Require Import ROSCOQ.StdlibMisc.

(*Move the 2 functions below to other file*)


Require Import interfaces.abstract_algebra.
Require Export Coq.Lists.List.

Instance InstanceDecidableEq {T:Type} {deq : DecEq T} (x y:T) : Decision (x ≡ y).
  apply eqdec.
Defined.


Instance InstanceDecidableIn {T:Type} {deq : DecEq T} (h:T) (l: list T) : Decision (In h l).
apply in_dec. apply eqdec.
Defined.

(*
copied from https://github.com/aa755/CFGV/blob/d230d5d0e4d63e49bb80484baed7c630215384ea/list.v#L3140
*)
Instance InstanceDecidableNoDup {T:Type} {deq : DecEq T} (l: list T) : Decision (NoDup l).
induction l; [apply left; constructor|].
  destruct (decide (In a l));[right | ].
  - intro Hin. inversion Hin; auto.
  - destruct IHl; [left; constructor; trivial| right].
    intro Hnt. inversion Hnt; auto.
Defined.

Global Instance EquivComparisonDecidable 
: Equiv Datatypes.comparison := eq.

Require Import 
CoRN.model.structures.Qpossec.
Global Instance DecEquivComparison (x y : Datatypes.comparison)
  : Decision (x=y).
Proof.
  apply comparison_eq_dec.
Qed.


(** the latter is more convenient, as it safes a step of interpreting boolean
values *)
Lemma bool_decide_sumbool `{Decision P} {T:Type} : forall (a b : T),
(if (bool_decide P) then  a  else b) ≡ 
(if (decide P) then a else b).
Proof using.
  intros ? ?.
  destruct (decide P) as [p|p].
- apply bool_decide_true in p; rewrite p. reflexivity. 
- apply bool_decide_false in p; rewrite p. reflexivity. 
Qed.


Require Import CoRN.logic.Stability.

Require MathClasses.implementations.bool.

Global Instance  stableBoolEq : ∀ (a b : bool),
MathClasses.misc.util.Stable (a = b).
Proof using.
  intros ? ? H.
  unfold DN in H.
  destruct a; destruct b; try auto;  try tauto; unfold util.DN in H.
  - unfold util.DN in H. setoid_rewrite not_false_iff_true in H. tauto.
  - setoid_rewrite not_true_iff_false in H. tauto.
Qed.

