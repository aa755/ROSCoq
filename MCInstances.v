Require Import MathClasses.interfaces.canonical_names.
Require Import CanonicalNotations.
Require Export core.
Instance Zero_instance_QTime : Zero QTime := (mkQTime 0 I).
Instance Zero_instance_Time : Zero Time := (QT2T (mkQTime 0 I)).
Instance Lt_instance_QTime : Lt QTime := Qlt.
Instance Le_instance_QTime : Le QTime := Qle.

Instance SqrtFun_instancee_IR : SqrtFun IR IR.
intros r. apply (sqrt (AbsIR r)). apply AbsIR_nonneg.
Defined.

Require Import interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.

Instance Zero_instance_IR : Zero IR := [0]. 
Instance One_instance_IR : One IR := [1]. 
Instance Plus_instance_IR : Plus IR := csg_op .
Instance Mult_instance_IR : Mult IR := cr_mult.
Instance Negate_instance_IR : Negate IR := cg_inv.
Instance : Ring IR.
Proof. apply (rings.from_stdlib_ring_theory (CRing_Ring IR)). Qed.
Instance Le_instance_IR : Le IR := (@cof_leEq IR).

Instance Cast_instace_Q_IR : Cast Q IR := (inj_Q IR).
