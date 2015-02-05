Require Import MathClasses.interfaces.canonical_names.
Require Import CanonicalNotations.
Require Export core.
Instance Zero_instance_QTime : Zero QTime := (mkQTime 0 I).
Instance Zero_instance_Time : Zero Time := (QT2T (mkQTime 0 I)).
Instance Zero_instance_IR : Zero IR := [0]. (** why not prove it is a ring *)

Instance SqrtFun_instancee_IR : SqrtFun IR IR.
intros r. apply (sqrt (AbsIR r)). apply AbsIR_nonneg.
Defined.

Instance Plus_instance_IR : Plus IR := csg_op .
Instance Mult_instance_IR : Mult IR := cr_mult.
Instance Negate_instance_IR : Negate IR := cg_inv.
Instance Cast_instace_Q_IR : Cast Q IR := (inj_Q IR).
(* Instance Lt_instace_Q_IR : Lt IR.
  intros a b. *)
