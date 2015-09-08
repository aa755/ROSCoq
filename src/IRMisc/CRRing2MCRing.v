
Section Conv.
Require Export CoRNMisc.
Variable (TContR : CRing).
Require Import MathClasses.interfaces.canonical_names.

Global Instance Zero_instance_TContR : Zero TContR := [0]. 
Global Instance One_instance_TContR : One TContR := [1]. 
Global Instance Plus_instance_TContR : Plus TContR := csg_op .
Global Instance Mult_instance_TContR : Mult TContR := cr_mult.
Global Instance Negate_instance_TContR : Negate TContR := cg_inv.

Require Export MathClasses.theory.rings.
Require Export MathClasses.interfaces.abstract_algebra.

Global Instance : Ring TContR.
Proof. apply (rings.from_stdlib_ring_theory (CRing_Ring TContR)). Qed.

End Conv.
