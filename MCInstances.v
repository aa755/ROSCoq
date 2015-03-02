Require Import MathClasses.interfaces.canonical_names.
Require Import CanonicalNotations.
Require Export core.
Instance Zero_instance_QTime : Zero QTime := (mkQTime 0 I).
Instance Zero_instance_Time : Zero Time := (QT2T (mkQTime 0 I)).
Instance Lt_instance_QTime : Lt QTime := Qlt.
Instance Le_instance_QTime : Le QTime := Qle.
Instance Plus_instance_QTime : Plus QTime := Qtadd.

Instance SqrtFun_instancee_IR : SqrtFun IR IR.
intros r. apply (sqrt (AbsIR r)). apply AbsIR_nonneg.
Defined.

Require Import interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.

Definition decAuto :  ∀ (P: Prop) `{Decision P},
  (if decide P then True else False) -> P.
  intros ? ? Hd.
  destruct (decide P); tauto.
Defined.

Require Export Psatz.
Lemma QTimeLeRefl : ∀ {t : QTime},
  t ≤ t.
intros.
unfold le, Le_instance_QTime; lra.
Qed.



Instance Zero_instance_IR : Zero IR := [0]. 
Instance One_instance_IR : One IR := [1]. 
Instance Plus_instance_IR : Plus IR := csg_op .
Instance Mult_instance_IR : Mult IR := cr_mult.
Instance Negate_instance_IR : Negate IR := cg_inv.
Instance : Ring IR.
Proof. apply (rings.from_stdlib_ring_theory (CRing_Ring IR)). Qed.
Instance Le_instance_IR : Le IR := (@cof_leEq IR).

Instance Zero_instance_TContR : Zero TContR := [0]. 
Instance One_instance_TContR : One TContR := [1]. 
Instance Plus_instance_TContR : Plus TContR := csg_op .
Instance Mult_instance_TContR : Mult TContR := cr_mult.
Instance Negate_instance_TContR : Negate TContR := cg_inv.
Instance : Ring TContR.
Proof. apply (rings.from_stdlib_ring_theory (CRing_Ring TContR)). Qed.


Instance Cast_instace_Q_IR : Cast Q IR := (inj_Q IR).


(** Equiv itself does not give RST props of equality *)
Instance Equivalence_instance_IR : @Equivalence IR equiv.
  split; repeat (intros ?); simpl; repnd; auto with *.
Defined.


Instance NormSpace_instance_Q : NormSpace Q Q := Qabs.Qabs.

Require Export CoRN.reals.fast.CRIR.
Instance Cart_CR_IR : Cast CR IR := CRasIR.

Instance Proper_CRasIR : Proper (@st_eq CR ==> @st_eq IR) CRasIR.
Proof.
  exact CRasIR_wd.
Qed.
Hint Unfold Le_instance_IR  Plus_instance_IR Negate_instance_IR 
    Mult_instance_IR: IRMC.
Hint Unfold π₁ ProjectionFst_instance_prod : π₁.

Hint Unfold Le_instance_IR  Plus_instance_IR Negate_instance_IR : IRMC.
Hint Unfold canonical_names.negate
  canonical_names.negate
  plus
  one zero
  equiv  mult
  dec_recip
  zero
  le
  lt
  canonical_names.negate
  Negate_instance_IR : 
 IRMC.
Hint Unfold Mult_instance_IR  : IRMC.
Hint Unfold mult plus one zero Mult_instance_TContR Plus_instance_TContR One_instance_TContR
    Zero_instance_TContR : TContRMC.
Hint Unfold Negate_instance_TContR : TContRMC.
