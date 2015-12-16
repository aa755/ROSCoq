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
Open Scope mc_scope.
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

Require Import MathClasses.interfaces.orders.

Global Instance LeIRPreorder  : PreOrder Le_instance_IR .
Proof.
  split; intros ?; unfold le, Le_instance_IR; eauto 2 with CoRN.
Qed.

Global Instance LeIRPartialOrder  : PartialOrder Le_instance_IR .
Proof.
  split; eauto with typeclass_instances.
  intros ? ?; unfold le, Le_instance_IR, equiv; eauto 2 with CoRN.
Qed.
 

Hint Unfold canonical_names.negate
  canonical_names.negate
  Le_instance_IR  
  Plus_instance_IR 
  Zero_instance_IR
  plus
  one zero
  equiv  mult
  dec_recip
  zero
  le
  lt
  canonical_names.negate
  Negate_instance_IR 
  Mult_instance_IR : IRMC.
  
Require Import MathClasses.orders.rings.

Global Instance OrderPreservingLePlusIR (z : IR):  OrderPreserving (plus z).
Proof.
  split; eauto  with typeclass_instances.
  - split; eauto with typeclass_instances.
    split;  eauto with typeclass_instances.
  - intros. apply plus_resp_leEq_lft; assumption.
Qed.

Global Instance MultLeSemiRingOrderIR:
  ∀ x y : IR , PropHolds (0 ≤ x) → PropHolds (0 ≤ y) → PropHolds (0 ≤ x * y) .
Proof.
  apply mult_resp_nonneg.
Qed.

Global Instance LeIRSemiRingOrder  : orders.SemiRingOrder (@le IR _).
Proof.
  apply from_ring_order; eauto with typeclass_instances.
Qed.


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



Require Export CoRN.reals.fast.CRIR.
Instance Cart_CR_IR : Cast CR IR := CRasIR.

Instance Proper_CRasIR : Proper (@st_eq CR ==> @st_eq IR) CRasIR.
Proof.
  exact CRasIR_wd.
Qed.

Hint Unfold π₁ ProjectionFst_instance_prod : π₁.


Hint Unfold mult plus one zero Mult_instance_TContR Plus_instance_TContR One_instance_TContR
    Zero_instance_TContR Negate_instance_TContR : TContRMC.

Global Instance Le_instance_Time : Le Time := fun x y => x [<=] y.

  (** The typeclass [Lt] is defined in the Prop universe. It cannot have constructive content.*)
Global Instance Lt_instance_Time : Lt Time := fun x y => Truncate (x [<] y).

Hint Unfold Le_instance_Time : IRMC.

Lemma timeLtWeaken : forall {a b: Time}, (a < b  -> a ≤ b)%mc.
Proof.
  intros ? ? H.
  destruct H as [X].
  (* autounfold with IRMC. unfold Le_instance_Time.
       info_eauto 2 with CoRN. *)
  apply less_leEq. exact X.
Qed.

Global Instance Equivalence_instance_Subcseteq  
  (S : CSetoid) (P : S → CProp) : 
      @Equivalence (subcsetoid_crr S P) (subcsetoid_eq S P).
pose proof (subcsetoid_equiv S P) as X. destruct X as [R  ST].
destruct ST as [T Sym].
split.
- exact R.
- exact Sym.
- exact T.
Qed.
  

Inductive pointWiseRelated {A:Type} (R : A-> A -> Prop): (list A) -> (list A) -> Prop :=
| prnil : pointWiseRelated R nil nil
| prcols : forall (hl hr : A) (tl tr : list A),
  R hl hr
  -> pointWiseRelated R tl tr
  -> pointWiseRelated R (hl::tl) (hr::tr).
  

(** same size and elements must be point-wise equal (upto [equiv])*)
Global Instance Equiv_List `{Equiv A} :  Equiv (list A) :=
  (pointWiseRelated equiv).

Global Instance Equivalence_List  `{Equiv A} `{@Equivalence A equiv} :
    @Equivalence (list A) equiv.
Proof.
  split.
  - intros l. induction l; constructor; eauto with relations.
  - intros l. induction l; intros ? Heq; inversion Heq;  constructor; 
    eauto with relations.
    apply IHl. eauto with relations.
  - intros l. induction l; intros ?  ? H1eq. inversion H1eq; subst.
    tauto.
    inversion H1eq.  subst. intros H2eq.
    inversion H2eq. subst.  constructor; 
    eauto with relations.
    eapply IHl; eauto with relations.
Qed.

Global Instance Equiv_List_Cons  `{Equiv A}  :
   Proper (equiv ==> equiv ==> equiv) cons.
Proof.
  intros ? ? ? ? ? ? .
  constructor; assumption.
Qed.


Global Instance LeTimeWd : Proper (equiv ==> equiv ==> iff) 
  (@canonical_names.le Time _).
Proof.
  intros x y H x0 y0 H0.
  autounfold with IRMC.
  autounfold with IRMC in H, H0.
  destruct x. destruct y.
  destruct x0. destruct y0.
  simpl in H, H0.
  unfold Le_instance_Time. simpl.
  rewrite H0, H. tauto. 
Qed.

Global Instance LtTimeWd : Proper (equiv ==> equiv ==> iff) (@lt Time _).
Proof.
  intros x y H x0 y0 H0.
  autounfold with IRMC.
  autounfold with IRMC in H, H0.
  destruct x. destruct y.
  destruct x0. destruct y0.
  simpl in H, H0.
  unfold Lt_instance_Time. simpl. 
  split; intros Hh; simpl in Hh;
  destruct Hh;  apply truncate;
  eauto using less_wdl, less_wdr.
  symmetry in H, H0.
  eauto using less_wdl, less_wdr.
Qed.

Lemma RingNegateProper `{Ring A} : Proper (equiv ==> equiv) (@negate A _).
Proof.
  intros ? ? Hh . rewrite Hh. reflexivity.
Qed.

Global Instance Pi_Instance_IR: RealNumberPi ℝ := Pi.Pi.
Global Instance HalfNumIR : HalfNum IR:= Half.

Open Scope mc_scope.
  Lemma PiBy2DesugarIR : ½ * π =  Pi.Pi [/]TwoNZ.
  Proof.
    rewrite mult_comm.
    apply mult_wd;[reflexivity|].
    apply (@mult_cancel_rht _ _ _ Two);[apply two_ap_zero|].
    unfold half_num, HalfNumIR, Half.
    unfold cf_div.
    rewrite <- mult_assoc_unfolded.
    rewrite field_mult_inv_op. ring.
  Qed.

  Global Instance ReflexiveTimeLe :
    Reflexive (@canonical_names.le Time _).
  Proof.
    intros a. apply leEq_reflexive.
  Qed.
    
   Global Instance StableEqIR : 
     forall x y : IR, Stable (x=y).
   Proof.
    intros ? ? Hd.
    apply not_ap_imp_eq. intros Hc. apply Hd. clear Hd.
    intro Hcc.
    apply ap_tight in Hc;auto.
  Qed.
  
   Global Instance StableLeIR : 
     forall x y : IR, Stable (x≤y).
   Proof.
    intros ? ? Hd. apply leEq_def.
    intro Hc. apply Hd. clear Hd. intro Hd. 
    apply leEq_def in Hd. apply Hd. assumption.
   Qed.


   Ltac hideRight :=
   match goal with
   | [|- _ = ?r] => remember r
   | [|- _ [=] ?r] => remember r
   | [|- eq _ ?r] => remember r
   end.

(*Move*)
  Global Instance ProperNoSignChange : forall F:TContR,
    Proper (equiv ==> equiv ==> iff) (noSignChangeDuring F).
  Proof.
    intros F ? ? H1e ? ? H2e.
    unfold noSignChangeDuring, nonNegDuring, nonPosDuring.
    destruct x,y,x0,y0.
    autounfold with IRMC in H1e, H2e.
    simpl. simpl in H1e, H2e.
    setoid_rewrite H1e.
    setoid_rewrite H2e.
    tauto.
  Qed.

Global Instance LeTimePreorder  : PreOrder Le_instance_Time .
Proof.
  split; intros ?; unfold le, Le_instance_Time; eauto 2 with CoRN.
Qed.

Global Instance LeTimePartialOrder  : PartialOrder Le_instance_Time.
Proof.
  split; eauto with typeclass_instances.
  intros ? ?; unfold le, Le_instance_Time, equiv; eauto 2 with CoRN.
  intros. destruct x, y. eapply leEq_imp_eq; eauto.
Qed.

