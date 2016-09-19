
Require Export CoRN.ftc.MoreIntervals.
Require Export IRMisc.PointWiseRing.
Require Import IRMisc.LegacyIRRing.

Set Implicit Arguments.
Require Import Coq.Unicode.Utf8.

Lemma csg_op_wd : forall (C: CSemiGroup) (x1 y1 x2 y2:C), 
  x1 [=] x2
  -> y1 [=] y2
  -> x1 [+] y1 [=] x2 [+] y2.
Proof.
  intros ? ? ? ? ? H1 H2.
  rewrite H1, H2. reflexivity.
Qed.

Lemma cg_inv_wd : forall (C: CGroup) (x1 x2 :C), 
  x1 [=] x2
  -> [--] x1  [=] [--] x2.
Proof.
  intros ? ? ?  H1.
  rewrite H1. reflexivity.
Qed.

(**
CoRN has a rich theory of continuous functions.
Continuous functions from Time to R 
are heavily used ROSCoq
to represent evolution of physical quntities.

In this file, wrap CoRN's theory of continuous functions
into a representation (IContR] where functions come bundled with
a proof of their continuity.
The main goal is to reduce verbosity and increase convenience,
by hiding the manipulation of continuity proofs for most
operations on continuous functions.
We show that [IContR] has a ring structure.
*)

Lemma interval_convex:
  ∀ (a b : IR) (I : interval),
    I a → I b → included (clcr a b) I.
Proof.
  intros ? ? ? Ha Hb. unfold included. intros x Hab.
  simpl in Hab. destruct Hab as [Hab Habr].
  destruct I; simpl in Ha, Hb; simpl; try (split; destruct Ha, Hb); 
    eauto using leEq_less_trans, leEq_reflexive, 
                less_leEq_trans, leEq_transitive.
Qed.

Hint Resolve less_Min leEq_Min : CoRN.

Lemma interval_Min:
  ∀ {a b : IR} {I : interval},
    I a → I b → I (Min a b).
Proof.
  intros ? ? ? Ha Hb.
  destruct I; simpl in Ha, Hb; simpl; try (split; destruct Ha, Hb);
    eauto using leEq_less_trans, leEq_reflexive, 
                 leEq_transitive,
                Min_leEq_lft, less_Min, leEq_Min.
Qed.

Lemma interval_Max:
  ∀ {a b : IR} {I : interval},
    I a → I b → I (Max a b).
Proof.
  intros ? ? ? Ha Hb.
  destruct I; simpl in Ha, Hb; simpl; try (split; destruct Ha, Hb);
  eauto using less_leEq_trans, leEq_reflexive, 
                leEq_transitive,
                lft_leEq_Max, Max_less, Max_leEq.
Qed.

Section ContFAlgebra.
Variable itvl : interval.

Definition RInIntvl := Build_SubCSetoid IR (itvl).

Definition mkRIntvl (r : IR) (p : (itvl) r) : RInIntvl := 
  (Build_subcsetoid_crr  _ _ r p).

Variable pItvl : proper itvl.

Definition somePtInIntvl : RInIntvl.
  apply proper_nonvoid in pItvl.
  apply nonvoid_point in pItvl.
  destruct pItvl as [x pf].
  exists x; trivial.
Defined.

  
Definition RI_R := 
    FS_as_PointWise_CRing RInIntvl  IR somePtInIntvl.


Definition toPart (f : RI_R) : PartIR.
  apply Build_PartFunct with (pfdom := (itvl)) 
    (pfpfun := fun ir pp => f (mkRIntvl ir pp)).
  - apply iprop_wd.
  - intros ? ? ? ?. apply csf_strext.
Defined.


Definition fromPart (f : PartIR) (Hd : included itvl (Dom f)): RI_R.
  apply Build_CSetoid_fun with
    (csf_fun := (fun x : RInIntvl 
        => f (scs_elem _ _ x) (Hd _  (scs_prf _ _ x)))).

  intros ? ? Hsep.
  apply (pfstrx _ f) in Hsep. simpl.
  unfold subcsetoid_ap, Crestrict_relation. simpl.
  destruct x, y. simpl in Hsep.
  trivial.
Defined.

Lemma toFromPartId : forall (F : PartIR) p,
  Feq itvl F (toPart (fromPart F p)).
Proof.
  intros ? ?.
  split; [trivial|].
  simpl. split;[apply included_refl|].
  intros ? ? ? ?.
  apply pfwdef.
  apply eq_reflexive_unfolded.
Qed.


Lemma toPartSum : forall (F G : RI_R),
  Feq itvl ((toPart F) {+} (toPart G))
           (toPart (F [+] G)).
Proof.
  intros ? ?. simpl.
  unfold FS_sg_op_pointwise, toPart.
  simpl.
  split; simpl;
    [apply included_conj; apply included_refl|].
  split;[apply included_refl|].
  intros. apply csbf_wd; apply csf_fun_wd;
  simpl; reflexivity.
Qed.

Lemma toPartMinus : forall (F G : RI_R),
  Feq itvl ((toPart F) {-} (toPart G))
           (toPart (F [-] G)).
Proof.
  intros ? ?. simpl.
  unfold FS_sg_op_pointwise, toPart.
  simpl.
  split; simpl;
    [apply included_conj; apply included_refl|].
  split;[apply included_refl|].
  intros. unfold cg_minus.
  apply csbf_wd; apply csf_fun_wd;
  simpl.
  reflexivity.
  apply csf_fun_wd.
  simpl. reflexivity.
Qed.

(** This proof is exactly same as [fromPartSum]
    above*)
Lemma toPartMult : forall (F G : RI_R),
  Feq itvl ((toPart F) {*} (toPart G))
           (toPart (F [*] G)).
Proof.
  intros ? ?. simpl.
  unfold FS_sg_op_pointwise, toPart.
  simpl.
  split; simpl; auto;
    [apply included_conj; apply included_refl|].
  split;[apply included_refl|].
  intros. apply csbf_wd; apply csf_fun_wd;
  simpl; reflexivity.
Qed.

Lemma toPartConst : forall (c:IR),
  Feq itvl ([-C-]c)
           (toPart ((Const_CSetoid_fun _ _ c))).
Proof.
  intros ?. simpl.
  split; simpl; [intro x ; auto |].
  split;[apply included_refl|].
  intros. reflexivity.
Qed.

Lemma toPartInv : forall (F : RI_R),
  Feq itvl (Finv (toPart F))
           (toPart ([--] F)).
Proof.
  intros ?. simpl.
  split; simpl; [intro x ; auto |].
  split;[apply included_refl|].
  intros. apply csf_fun_wd.
  apply csf_fun_wd.
  simpl. reflexivity.
Qed.

Lemma extToPart (f : RI_R) : forall (x:IR) (p : (itvl) x) 
  (p' : Dom (toPart f) x), 
      f (mkRIntvl x p) [=] (toPart f) x p'.
Proof.
  intros ? ? ?.
  simpl. apply csf_fun_wd.
  simpl. reflexivity.
Qed.

Lemma extToPartLt (f : RI_R) : forall (x y:IR) 
  (px : (itvl) x) (py : (itvl) y)
  (px': Dom (toPart f) x) (py': Dom (toPart f) y), 
    f (mkRIntvl x px) [<] f (mkRIntvl y py)
    -> (toPart f) x px' [<] (toPart f) y py'.
Proof.
  intros ? ? ? ? ? ? Hlt.
  pose proof (extToPart f x px px') as Hx.
  pose proof (extToPart f y py py') as Hy.
  eauto using less_wdl, less_wdr.
Qed.

Lemma extToPartLt2 (f : RI_R) : forall x y,
    f x [<] f y
    -> (toPart f) x (scs_prf _ _ x) 
        [<] (toPart f) y (scs_prf  _ _ y).
Proof.
  intros. destruct x,y. eapply extToPartLt; eauto.
Qed.

Lemma extToPart2 (f : RI_R) : forall (x:IR) (p : (itvl) x),
  f (mkRIntvl x p) [=] (toPart f) x p.
Proof.
  intros ? ?.
  simpl. apply csf_fun_wd.
  simpl. reflexivity.
Qed.


Lemma extToPart3 (f : RI_R) : forall (t : RInIntvl),
  (f  t) [=] (toPart f) t (scs_prf _ _ t).
Proof.
  intros ?.
  destruct t.
  simpl.
  apply extToPart2.
Qed.

Lemma st_eq_Feq : forall (f g : RI_R),
  f [=] g
  -> Feq itvl (toPart f) (toPart g).
Proof.
  intros. unfold Feq. simpl. 
  split; [ eauto 1 with included |].
  split; [ eauto 1 with included |].
  intros ? ? ? ?.
  apply FS_as_CSetoid_proper; trivial.
  simpl. reflexivity.
Qed.

Lemma intvlIncluded : forall (ta tb : RInIntvl),
  included (clcr ta tb) (itvl).
Proof.
  destruct ta as [ra pa].
  destruct tb as [rb pb].
  simpl. apply interval_convex; trivial.
Defined.

Definition TMin (ta tb :RInIntvl) : RInIntvl:= 
  {|
    scs_elem := Min ta tb;
    scs_prf := interval_Min (scs_prf _ _ ta) (scs_prf _ _ tb) |}.

Definition TMax (ta tb :RInIntvl) : RInIntvl:= 
  {|
    scs_elem := Max ta tb;
    scs_prf := interval_Max (scs_prf _ _ ta) (scs_prf _ _ tb) |}.

Lemma intvlIncludedCompact : forall (a b : RInIntvl) (Hab : a [<=] b),
  included (Compact Hab) itvl.
Proof.
  intros. apply (intvlIncluded).
Qed.


Lemma st_eq_Feq_included : forall (f g : RI_R) (a b : RInIntvl) (Hab : a [<=] b),
  f [=] g
  -> Feq (Compact Hab) (toPart f) (toPart g).
Proof.
  intros. eapply included_Feq; [| apply st_eq_Feq].
  apply (intvlIncluded). trivial.
Qed.

Require Export SubCRing.
Require Export CoRN.ftc.MoreFunctions.
Definition IContR : CRing.
  apply (SubCRing RI_R
        (fun f => Continuous itvl (toPart f))); auto.
- intros f g Hcf Hcg.
  eapply Continuous_wd;
    [apply toPartSum|].
  apply Continuous_plus; trivial.
- simpl. eapply Continuous_wd;
    [apply toPartConst|].
  apply Continuous_const; trivial.
- intros f Hcf.
  eapply Continuous_wd;
    [apply toPartInv|].
  apply Continuous_inv; trivial.
- intros f g Hcf Hcg.
  eapply Continuous_wd;
    [apply toPartMult|].
  apply Continuous_mult; trivial.
- simpl. eapply Continuous_wd;
    [apply toPartConst|].
  apply Continuous_const; trivial.
Defined.


Definition getF  (f : IContR) : RI_R :=
  (scs_elem _ _ f).

Definition ContConstFun (v : IR) : IContR.
  eexists.
  eapply Continuous_wd;
    [apply (toPartConst v)|].
  apply Continuous_const; trivial.
Defined.

Global Instance ContConstFun_wd : Proper (@st_eq IR ==> @st_eq IContR) ContConstFun.
Proof.
  intros ? ? Heq z. simpl. exact Heq.
Qed.
 


  
Definition IContRId : IContR.
 eexists.
 eapply Continuous_wd;[apply toFromPartId|]. apply Continuous_id.
 Unshelve. intros ? ? . simpl. auto.
Defined.


Notation "{ f }" := (getF f).

Lemma IContRPlusAp : ∀ (F G: IContR) t,
  {F [+] G} t [=] {F} t [+] {G} t.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Lemma IContRMinusAp : ∀ (F G: IContR) t,
  {F [-] G} t [=] {F} t [-] {G} t.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Lemma IContRInvAp : ∀ (F: IContR) t,
  {[--] F} t [=] [--] ({F} t).
Proof.
  intros. simpl.
  reflexivity.
Qed.


Lemma IContRConstAp : ∀ (c: IR) t,
  {ContConstFun c} t [=] c.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Lemma IContRIdAp : ∀ t,
  {IContRId} t [=] t.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Lemma IContRMultAp : ∀ (F G: IContR) t,
  {F [*] G} t [=] {F} t [*] {G} t.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Hint Rewrite IContRInvAp IContRConstAp IContRPlusAp IContRMultAp IContRMinusAp : IContRApDown.

Require Import CoRNMisc.


Lemma toPartMultIContR : forall (F G : IContR),
  Feq itvl ((toPart F) {*} (toPart G))
           (toPart (F [*] G)).
Proof.
  intros ? ?. destruct F, G.
  simpl. apply toPartMult.
Qed.

Lemma toPartPlusIContR : forall (F G : IContR),
  Feq itvl ((toPart F) {+} (toPart G))
           (toPart (F [+] G)).
Proof.
  intros ? ?. destruct F, G.
  simpl. apply toPartSum.
Qed.

Lemma FConstOppIn : ∀ (c : IR),
  [--](ContConstFun c) [=] (ContConstFun ([--]c)).
Proof.
  intros c.
  simpl.
  intros x.
  simpl.
  reflexivity.
Qed.

Lemma TContRInvAsMult : ∀ (F: IContR),
   (ContConstFun ([--] [1]) [*] F)[=] [--] F.
Proof.
  intros F. rewrite <- FConstOppIn.
  symmetry.
  rewrite <- mult_minus1.
  reflexivity.
Qed.


Lemma ExtEqIContR : ∀ (F G : IContR),
  (∀ a, {F} a [=] {G} a) -> F [=] G.
Proof.
  intros ? ?. destruct F, G.
  simpl.
  intros Heq.
  exact Heq.
Qed.

Lemma FConstMult : ∀ (a b: IR), (ContConstFun a) [*] (ContConstFun b) 
                                  [=] (ContConstFun (a[*]b)).
Proof.
  intros a b x. simpl. reflexivity.
Qed.


Hint Resolve (scs_prf IR (itvl)) : CoRN.




Lemma IContRCont : forall (tf : IContR) (ta tb : RInIntvl), 
    Continuous  (clcr ta tb) (toPart tf).
Proof.
  intros ? ? ?.
  pose proof (scs_prf _ _ tf) as Hc.
  simpl in Hc.
  eapply Included_imp_Continuous; eauto.
  apply intvlIncluded.
Defined.

Lemma IContRCont_I : ∀ (f : IContR) {l r : RInIntvl} 
    (p : l[<=]r), 
    Continuous_I p (toPart f).
Proof.
  intros ? ? ? ?.
  pose proof (IContRCont f l r) as Hc.
  unfold Continuous in Hc.
  apply Hc.
  unfold compact, iprop.
  apply included_refl.
Defined.

Lemma TMin_LeEq_Max : ∀ a b : RInIntvl , 
    TMin a b[<=] TMax a b.
Proof.
  intros ? ?. simpl. apply Min_leEq_Max.
Qed.

Lemma IContRCont_IMinMax : ∀ (f : IContR) (l r : RInIntvl), 
    Continuous_I (TMin_LeEq_Max l r) (toPart f).
Proof.
  intros ? ? ?.
  apply IContRCont_I.
Defined.

(*
Definition CIntegral (l r : RInIntvl) (f : IContR) : IR :=
  integral  _ _ _ _ (IContRCont_IMinMax f l r).
*)

Definition IntgBnds : CSetoid :=
  Build_SubCSetoid (ProdCSetoid RInIntvl RInIntvl) (fun p => fst p [<=] snd p).

Definition intgBndL (ib : IntgBnds) : RInIntvl:=  (fst (scs_elem _ _ ib)).
Definition intgBndR (ib : IntgBnds) : RInIntvl:=  (snd (scs_elem _ _ ib)).


Definition Cintegral
    (lr : IntgBnds)
    (f : IContR) : IR :=
  integral _ _ _ _ (IContRCont_I f (scs_prf _ _ lr)).

Global Instance Cintegral_wd : Proper 
    ((@st_eq (Build_SubCSetoid (ProdCSetoid RInIntvl RInIntvl) (fun p => fst p [<=] snd p)))
      ==> (@st_eq IContR) 
      ==> (@st_eq IR)) (Cintegral).
Proof.
  intros pa pb Hp f g Hfg.
  unfold Cintegral.
  destruct pa as [lr pa]. destruct lr as [la ra].
  destruct pb as [lr pb]. destruct lr as [lb rb].
  simpl.
  pose proof (integral_wd' _ _ _ _ 
    (IContRCont_I f pa) _ _ _ (IContRCont_I f pb)) as HH.
  simpl in HH. destruct la,lb,ra,rb. simpl in HH, Hp. 
  simpl. specialize (HH (proj1 Hp) (proj2 Hp)).
  rewrite HH.
  apply integral_wd.
  pose proof (@st_eq_Feq_included f g) as Hst.
  match goal with
  [ |- Feq (Compact ?vc) _ _] => match type of vc with
                                 CSetoids.scs_elem _ _ ?a [<=] CSetoids.scs_elem _ _ ?b =>  
                                    specialize (Hst a b)
                                 end
  end.
  simpl in Hst. apply Hst. destruct f, g. trivial.
Qed.

Definition inBounds (ib : IntgBnds) (x : IR) : Prop :=
  ((fst (scs_elem _ _ ib)) [<=] x ∧ x  [<=] (snd (scs_elem _ _ ib))).

Definition IContREqInIntvl (ib : IntgBnds) (f g : IContR) :=
(∀ x : RInIntvl, inBounds ib x -> {f} x [=] {g} x).

Global Instance Cintegral_wd2 (ib : IntgBnds) : 
    Proper 
      ((IContREqInIntvl ib) ==> (@st_eq IR)) 
      (Cintegral ib).
Proof.
  intros f g Hfg.
  unfold Cintegral.
  apply integral_wd.
  split;[unfold toPart; simpl; apply intvlIncludedCompact|].
  split;[unfold toPart; simpl; apply intvlIncludedCompact|].
  intros x Hc Hx Hx'.
  unfold compact in Hc. rewrite <- extToPart2, <- extToPart2.
  destruct Hc.
  erewrite csf_fun_wd;
    [ apply Hfg;
      split; auto |].
  simpl. reflexivity.
Qed.

Definition isIDerivativeOf (F' F : IContR) : CProp :=
  Derivative _ pItvl (toPart F) (toPart F').

Lemma IContR_st_eq_Feq : forall (f g : IContR),
  f [=] g
  -> Feq itvl (toPart f) (toPart g).
Proof.
  intros ? ? Heq.
  destruct f, g.
  simpl. apply st_eq_Feq.
  assumption.
Qed.

Lemma isIDerivativeOfWdl : ∀ (F1' F2' F : IContR),
  F1' [=] F2'
  -> isIDerivativeOf F1' F
  -> isIDerivativeOf F2' F.
Proof.
  unfold isIDerivativeOf.
  intros  ? ? ? Heq Hd.
  apply IContR_st_eq_Feq in Heq.
  eapply Derivative_wdr; eauto.
Qed.

Lemma isIDerivativeOfWdr : ∀ (F1 F2 F' : IContR),
  F1 [=] F2
  -> isIDerivativeOf F' F1
  -> isIDerivativeOf F' F2.
Proof.
  unfold isIDerivativeOf.
  intros  ? ? ? Heq Hd.
  apply IContR_st_eq_Feq in Heq.
  eapply Derivative_wdl; eauto.
Qed.


Lemma TContRDerivativeMult:
  ∀ (F F' G G' : IContR),
  isIDerivativeOf F' F
  → isIDerivativeOf G' G 
  → isIDerivativeOf  (F [*] G' [+] F' [*] G) (F [*] G).
Proof.
  intros  ? ? ? ?  H1d H2d.
  unfold isIDerivativeOf.
  eapply Derivative_wdl;[
    apply toPartMultIContR|].
  eapply Derivative_wdr;[
    apply toPartPlusIContR|].
  eapply Derivative_wdr;
    [apply Feq_plus; apply toPartMultIContR|].
  apply Derivative_mult; assumption.
Qed.

Lemma TContRDerivativeConst:
  ∀ (c : IR),
    isIDerivativeOf  [0] (ContConstFun c).
Proof.
  intros.
  unfold isIDerivativeOf.
  eapply Derivative_wdl;[
    apply toPartConst|].
  eapply Derivative_wdr;[
    apply toPartConst|].
  apply Derivative_const.
Qed.

Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Add Ring IRisaRing: (CRing_Ring IContR).

Lemma TContRDerivativeMultConstR:
  ∀ (F F' : IContR) (c : IR),
  isIDerivativeOf F' F
  → isIDerivativeOf  (F' [*] ContConstFun c) (F [*] ContConstFun c).
Proof.
  intros  ? ? ?  H1d.
  eapply isIDerivativeOfWdl;[
    |apply TContRDerivativeMult]; eauto;
    [| apply TContRDerivativeConst].
  ring.
Qed.

Lemma TContRDerivativeMultConstL:
  ∀ (F F' : IContR) (c : IR),
  isIDerivativeOf F' F
  → isIDerivativeOf  (ContConstFun c [*] F') (ContConstFun c [*] F).
Proof.
  intros  ? ? ?  H1d.
  eapply isIDerivativeOfWdl;
  [| eapply isIDerivativeOfWdr];
  [| | apply TContRDerivativeMultConstR]; eauto.
  instantiate (1:=c).
  ring.
  ring.
Qed.


Lemma TContRDerivativePlus:
  ∀ (F F' G G' : IContR),
  isIDerivativeOf F' F
  → isIDerivativeOf G' G 
  → isIDerivativeOf  (F' [+] G') (F [+] G).
Proof.
  intros  ? ? ? ?  H1d H2d.
  unfold isIDerivativeOf.
  eapply Derivative_wdl;[
    apply toPartPlusIContR|].
  eapply Derivative_wdr;[
    apply toPartPlusIContR|].
  apply Derivative_plus; assumption.
Qed.


Lemma TContRDerivativeOpp:
  ∀ (F F' : IContR),
  isIDerivativeOf F' F
  → isIDerivativeOf  ([--] F') ([--] F).
Proof.
  intros  ? ? H1d.
  eapply isIDerivativeOfWdl;
  [apply TContRInvAsMult| eapply isIDerivativeOfWdr];
  [apply TContRInvAsMult| ].
  apply TContRDerivativeMultConstL.
  assumption.
Qed.


Lemma IsDerivativeOne : isIDerivativeOf [1] (IContRId).
Proof.
  unfold isIDerivativeOf, IContRId. simpl.
  eapply Derivative_wdl;[apply toFromPartId |].
  eapply Derivative_wdr;[apply toPartConst |].
  apply Derivative_id.
Qed.

Lemma TContRDerivativeLinear:
  ∀ (a b : IR),
  isIDerivativeOf  (ContConstFun a) 
                  (ContConstFun b [+] ContConstFun a [*] IContRId).
Proof.
  intros  ? ?.
  eapply isIDerivativeOfWdl;[ apply cm_lft_unit_unfolded |].
  apply TContRDerivativePlus;[apply TContRDerivativeConst |].
  eapply isIDerivativeOfWdl;[ apply mult_one |].
  apply TContRDerivativeMultConstL.
  apply IsDerivativeOne.
Qed.

Local Notation "2" := ([1] [+] [1]).

Lemma DerivativeSqr:
  ∀ (F F' : IContR),
  isIDerivativeOf F' F
  → isIDerivativeOf  (2 [*] (F [*] F')) (F [*] F).
Proof.
  intros ? ? Hd.
  assert ( F [*] F' [+] F' [*] F [=] 2 [*] (F [*] F')) as Heq by ring.
  eapply isIDerivativeOfWdl in Heq; eauto.
  apply TContRDerivativeMult;
  assumption.
Qed.

Lemma DerivativeNormSqr:
  ∀ (X X' Y Y' : IContR),
  isIDerivativeOf X' X
  → isIDerivativeOf Y' Y
  → isIDerivativeOf  (2 [*] (X [*] X' [+] Y [*] Y')) 
                      (X [*] X [+] Y [*] Y).
Proof.
  intros ? ? ? ? H1d H2d.
  eapply isIDerivativeOfWdl;
    [symmetry; apply ring_dist_unfolded|].
  apply TContRDerivativePlus; apply DerivativeSqr; assumption.
Qed.

Lemma isDerivativeUnique:
  ∀ (F F1' F2' : IContR),
  isIDerivativeOf F1' F
  → isIDerivativeOf F2' F
  → F1' [=]  F2'.
Proof.
  intros ? ? ? H1d H2d.
  unfold isIDerivativeOf in H1d, H2d.
  eapply Derivative_unique in H1d; eauto.
  destruct F1'.
  destruct F2'.
  simpl.
  intros x.
  simpl in H1d.
  unfold Feq in H1d.
  apply snd in H1d.
  apply snd in H1d.
  rewrite extToPart3.
  rewrite extToPart3.
  symmetry.
  apply H1d.
  destruct x.
  simpl.
  assumption.
Qed.

Lemma TContRExt : forall (f : IContR) a b,
  a [=] b -> {f} a [=] {f} b.
Proof.
  intro f. apply  csf_fun_wd.
Qed.


Global Instance IContR_proper :
  Proper ((@st_eq IContR)
      ==> (@st_eq (RI_R))) (getF).
Proof.
  intros ? ? Heq. unfold getF.
  destruct x, y.
  simpl.
  simpl in Heq.
  exact Heq.
Qed.

Definition mkIntBnd {a b : RInIntvl} 
    (p : a [<=] b) : IntgBnds.
  exists (a,b).
  exact p.
Defined.

Lemma IDerivativeLB :forall {F F' : IContR}
   (ta tb : RInIntvl) (Hab : ta[<]tb) (c : IR),
   isIDerivativeOf F' F
   -> LBoundInCompInt Hab (toPart F') c
   -> c[*](tb[-]ta) [<=] ((getF F) tb[-] (getF F) ta).
Proof.
 intros ? ? ? ? ? ? Hisd Hub.
 rewrite extToPart3.
 rewrite extToPart3.
 apply (AntiderivativeLB2 (toPart F) (toPart F') ta tb Hab); auto.
 unfold isIDerivativeOf in Hisd.
 apply Included_imp_Derivative with 
   (I:=itvl) (pI := pItvl ); trivial;[].
 apply intvlIncluded.
Qed.


Lemma IDerivativeLB2 :forall (F F' : IContR)
   (ta tb : RInIntvl) (Hab : ta[<]tb) (c : IR),
   isIDerivativeOf F' F
   -> (forall (t:RInIntvl), (clcr ta tb) t -> c [<=] ({F'} t))
   -> c[*](tb[-]ta) [<=] ({F} tb[-] {F} ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  eapply IDerivativeLB with (Hab0 := Hab); eauto;[].
  unfold UBoundInCompInt.
  intros r Hc ?.
   unfold compact in Hc.
  unfold getF in Hub.
  pose proof Hc as Hccc.
  simpl in Hx.
  destruct Hc as [Hca Hcb].
  specialize (Hub {|scs_elem := r; scs_prf := Hx|} ).
  rewrite <- extToPart2.
  unfold getF in Hub.
  apply Hub.
  split; auto.
Qed.


(** double negation trick, to strengthen LB2. The hypothesis
ta[<=]tb was ta[<]tb before*)
Lemma IDerivativeLB3 :forall (F F' : IContR)
   (ta tb : RInIntvl) (Hab : ta[<=]tb) (c : IR),
   isIDerivativeOf F' F
   -> (forall (t:RInIntvl), (clcr ta tb) t -> c [<=] ({F'} t))
   -> c[*](tb[-]ta) [<=] ({F} tb[-] {F} ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  pose proof (leEq_less_or_equal _ _ _ Hab) as Hdec.
  apply leEq_def.
  intros Hc.
  apply Hdec. clear Hdec. intros Hdec.
  revert Hc. apply leEq_def.
  destruct Hdec as [Hlt | Heq].
  - eapply IDerivativeLB2; eauto.
  - rewrite Heq.
    rewrite cg_minus_correct.
    rewrite mult_commutes.
    rewrite cring_mult_zero_op.
    apply eq_imp_leEq. symmetry. apply x_minus_x.
    symmetry. apply TContRExt.
    simpl. destruct ta, tb. exact Heq.
Qed.

(** proof of the 3 lemmas below are the exact duals of the above "LB" versions  *)
Lemma IDerivativeUB :forall {F F' : IContR}
   (ta tb : RInIntvl) (Hab : ta[<]tb) (c : IR),
   isIDerivativeOf F' F
   -> UBoundInCompInt Hab (toPart F') c
   -> ((getF F) tb[-] (getF F) ta) [<=] c[*](tb[-]ta).
Proof.
 intros ? ? ? ? ? ? Hisd Hub.
 rewrite extToPart3.
 rewrite extToPart3.
 apply (AntiderivativeUB2 (toPart F) (toPart F') ta tb Hab); auto.
 unfold isIDerivativeOf in Hisd.
 apply Included_imp_Derivative with 
   (I:=itvl) (pI := pItvl ); trivial;[].
 apply intvlIncluded.
Qed.

Lemma IDerivativeUB2 :forall (F F' : IContR)
   (ta tb : RInIntvl) (Hab : ta[<]tb) (c : IR),
   isIDerivativeOf F' F
   -> (forall (t:RInIntvl), (clcr ta tb) t -> ({F'} t) [<=] c)
   -> ({F} tb[-] {F} ta) [<=] c[*](tb[-]ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  eapply IDerivativeUB with (Hab0 := Hab); eauto;[].
  unfold UBoundInCompInt.
  intros r Hc ?.
   unfold compact in Hc.
  unfold getF in Hub.
  pose proof Hc as Hccc.
  simpl in Hx.
  destruct Hc as [Hca Hcb].
  specialize (Hub {|scs_elem := r; scs_prf := Hx|} ).
  rewrite <- extToPart2.
  unfold getF in Hub.
  apply Hub.
  split; auto.
Qed.

Lemma IDerivativeUB3 :forall (F F' : IContR)
   (ta tb : RInIntvl) (Hab : ta[<=]tb) (c : IR),
   isIDerivativeOf F' F
   -> (forall (t:RInIntvl), (clcr ta tb) t -> ({F'} t) [<=] c)
   -> ({F} tb[-] {F} ta) [<=] c[*](tb[-]ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  pose proof (leEq_less_or_equal _ _ _ Hab) as Hdec.
  apply leEq_def.
  intros Hc.
  apply Hdec. clear Hdec. intros Hdec.
  revert Hc. apply leEq_def.
  destruct Hdec as [Hlt | Heq].
  - eapply IDerivativeUB2; eauto.
  - rewrite Heq.
    rewrite cg_minus_correct.
    rewrite mult_commutes.
    rewrite cring_mult_zero_op.
    apply eq_imp_leEq. symmetry. 
    symmetry. apply x_minus_x.
    symmetry. apply TContRExt.
    simpl. destruct ta, tb. exact Heq.
Qed.


Lemma nonDecreasingIfIDerivNonNeg :∀  (F F' : IContR)
   (tstart tend : RInIntvl) (Hab : tstart[<=]tend),
   isIDerivativeOf F' F
   -> (∀  (t: RInIntvl), (tstart [<=] t /\ t [<=] tend) -> [0] [<=] ({F'} t))
   -> ({F} tstart) [<=] ({F} tend).
Proof.
  intros ? ? ? ? ?  Hder Hn.
  pose proof (@IDerivativeLB3 F F' _ _ Hab [0] Hder) as X.
  rewrite cring_mult_zero_op in X.
  apply shift_leEq_rht. apply X. intros t Hb.
  apply Hn. simpl in Hb. destruct Hb. split; assumption.
Qed.

(** This is slightly stronger than [Barrow2]
    because it uses [cof_less] instead of [cof_leEq] *)
Lemma TBarrow : forall (F F': IContR)
         (der : isIDerivativeOf F' F) (a b : RInIntvl)
          (p: a [<=] b),
       Cintegral (mkIntBnd p) F' [=] {F} b [-] {F} a.
Proof.
  intros ? ? ? ? ? ?.
  unfold Cintegral.
  simpl.
  pose proof (Barrow _ _ (scs_prf _ _ F') pItvl _ der a b 
      (IContRCont_IMinMax _ _ _) (scs_prf _ _ a) (scs_prf _ _ b)) as Hb.
  simpl in Hb.
  rewrite TContRExt with (b:=b) in Hb by (destruct b; simpl; reflexivity).
  remember ({F} b) as hide.
  rewrite TContRExt with (b:=a) in Hb by (destruct a; simpl; reflexivity).
  subst hide.
  rewrite <- Hb. 
  rewrite Integral_integral.
  reflexivity.
Qed.

(** This is slightly stronger than [Barrow2]
    because it uses [cof_less] instead of [cof_leEq] *)
Lemma TBarrowEta : forall (F F': IContR)
         (der : isIDerivativeOf F' F) (ib: IntgBnds),
       Cintegral ib F' [=] {F} (snd (scs_elem _ _ ib)) [-] {F} (fst (scs_elem _ _ ib)).
Proof.
  intros ? ? ? ?.
  destruct ib.
  simpl. apply TBarrow; assumption.
Qed.

Lemma includeMinMaxIntvl : 
  forall (a b : RInIntvl),
    included (Compact (TMin_LeEq_Max a b)) itvl.
Proof.
  intros.
  match goal with
    [ |- included (Compact ?vc) _] => match type of vc with
                                   CSetoids.scs_elem _ _ ?a [<=] CSetoids.scs_elem _ _ ?b =>  
                                   specialize (intvlIncluded a b)
                                   end
  end.
  intros Hx.
  unfold compact. simpl.
  simpl in Hx. trivial.
Qed.



Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Lemma CIntegral_scale : ∀ (ib: IntgBnds) c (F : IContR),
   Cintegral ib (ContConstFun c [*] F) 
    [=] c [*] (Cintegral ib F).
Proof.
  intros.
  unfold Cintegral.
  rewrite <- integral_comm_scal.
  apply integral_wd.
  apply Feq_symmetric.
  eapply included_Feq.
  Focus 2. unfold Fscalmult.
  eapply Feq_transitive.
  Focus 2. apply toPartMult; fail.
  apply Feq_mult;
    [apply toPartConst |apply IContR_st_eq_Feq; reflexivity]; fail.
  simpl. apply intvlIncluded.
  Grab Existential Variables.
  eapply Continuous_I_wd.
  eapply included_Feq.
  Focus 2. apply Feq_symmetric. 
  eapply Feq_transitive.
  Focus 2. apply toPartMult; fail.
  apply Feq_mult;
    [apply toPartConst |apply IContR_st_eq_Feq; reflexivity]; fail.
  simpl. apply intvlIncluded; fail.
  eapply included_imp_Continuous. apply (scs_prf _ _ (((ContConstFun  c)[*]F))).
  simpl. apply intvlIncluded.
Qed.


Section CIntegralArith.
Context {a b : RInIntvl} (p : a [<=] b).
Variable (F G : IContR).

Lemma CIntegral_plus : 
   Cintegral (mkIntBnd p) (F [+] G) 
    [=] Cintegral (mkIntBnd p) F [+] Cintegral (mkIntBnd p) G.
Proof.
  unfold Cintegral.
  erewrite <- integral_plus; eauto.
  apply integral_wd.
  apply Feq_symmetric.
  eapply included_Feq;[|apply toPartSum]; eauto.
  simpl. apply intvlIncluded.
  Grab Existential Variables.
  eapply Continuous_I_wd.
  eapply included_Feq.
  Focus 2. apply Feq_symmetric. apply toPartSum; fail.
           simpl. apply intvlIncluded; fail.
  eapply included_imp_Continuous. apply (scs_prf _ _ (F [+]G)).
  simpl. apply intvlIncluded.
Qed.

Lemma CIntegral_minus : 
   Cintegral (mkIntBnd p) (F [-] G) 
    [=] Cintegral (mkIntBnd p) F [-] Cintegral (mkIntBnd p) G.
Proof.
  unfold Cintegral.
  erewrite <- integral_minus; eauto.
  apply integral_wd.
  apply Feq_symmetric.
  eapply included_Feq;[|apply toPartMinus]; eauto.
  simpl. apply intvlIncluded.
  Grab Existential Variables.
  eapply Continuous_I_wd.
  eapply included_Feq.
  Focus 2. apply Feq_symmetric. apply toPartMinus; fail.
           simpl. apply intvlIncluded; fail.
  eapply included_imp_Continuous. apply (scs_prf _ _ (F [-]G)).
  simpl. apply intvlIncluded.
Qed.


Lemma CIntegral_opp : 
   Cintegral (mkIntBnd p) ([--] G) 
    [=] [--] (Cintegral (mkIntBnd p) G).
Proof.
  unfold Cintegral.
  erewrite <- integral_inv; eauto.
  apply integral_wd.
  apply Feq_symmetric.
  eapply included_Feq; [|apply toPartInv]; eauto.
  simpl. apply intvlIncluded.
  Grab Existential Variables.
  eapply Continuous_I_wd.
  eapply included_Feq.
  Focus 2. apply Feq_symmetric. apply toPartInv; fail.
           simpl. apply intvlIncluded; fail.
  eapply included_imp_Continuous. apply (scs_prf _ _ ([--]G)).
  simpl. apply intvlIncluded.
Qed.

End CIntegralArith.



Section CIntegralProps.
Context {a b : RInIntvl} (p : a [<=] b).

(* Can be proved using TBarrow and isIderivative props.*)
Lemma CintegralConst : forall (c: IR),
   Cintegral (mkIntBnd p) (ContConstFun c) [=] c [*] (b [-] a).
Proof.
  intros ?.
  unfold Cintegral. simpl.
  rewrite <- integral_const.
  apply integral_wd.
  apply Feq_symmetric.
  eapply included_Feq;
    [apply intvlIncludedCompact |].
  apply toPartConst.
  Grab Existential Variables.
  apply Continuous_I_const.
Qed.

Lemma CintegralZero : 
   Cintegral (mkIntBnd p) [0] [=] [0].
Proof.
  setoid_rewrite CintegralConst.
  ring.
Qed.

Variable (F : IContR).
Lemma CintegralSplit : forall (c:RInIntvl)
   (pl : a [<=] c) (pr : c [<=] b),
   Cintegral (mkIntBnd p) F [=] Cintegral (mkIntBnd pl) F 
                                [+] Cintegral (mkIntBnd pr) F.
Proof.
  intros ? ? ?.
  unfold Cintegral.
  simpl. symmetry. apply integral_plus_integral. 
Qed.


Variable (G : IContR).

Lemma IntegralMonotone : 
   (forall (r: RInIntvl), (clcr (TMin a b) (TMax a b) r) -> {F} r[<=] {G} r)
   -> Cintegral (mkIntBnd p) F [<=] Cintegral (mkIntBnd p) G.
Proof.
  intros Hle.
  unfold Cintegral.
  simpl. apply monotonous_integral.
  intros ? Hc ? ?. rewrite <- extToPart2.
  rewrite <- extToPart2.
  specialize (Hle (mkRIntvl x Hx)).
  eapply leEq_transitive.
  apply Hle. unfold compact in Hc.
  destruct Hc. simpl. split; eauto 3 with CoRN.
  erewrite csf_fun_wd;[ apply leEq_reflexive | ].
  simpl. reflexivity.
Qed.


End CIntegralProps.


(** holds in general for groups. Move. *)
Lemma invInvIContR : forall (r:IContR), [--][--]r [=] r.
Proof.
  intros  ?. ring.
Qed.

(** holds in general for groups. Move. *)
Lemma invInvIR : forall (r:IR), [--][--]r [=] r.
Proof.
  intros  ?. ring.
Qed.


End ContFAlgebra.

(*
Definition ContFSG : CSemiGroup.

Definition ContFMonoid : CMonoid.

Definition ContFGroup : CGroup.

Definition ContFAbGroup : CAbGroup.

Definition ContFRing : CRing.

Definition ContField : CField.
*)

(** The definitions below talk about different intervals of continuity *)

(* Continuous_Sin Continuous_com *)
Require Export CoRN.transc.Trigonometric.

(** Compose two conttinuous functions.
This just ports the underlying composition function of CoRN
to the IContR type where functions are bundled with their continuoity proofs *)

Definition composeIContRGeneral 
  (I J : interval) (pI : proper I) (pJ : proper J)
  (F : IContR J pJ) (theta : IContR I pI)
  (mp: maps_compacts_into_weak I J (toPart theta)) : IContR I pI.
  pose proof (scs_prf _ _  theta) as Hc.
  pose proof (scs_prf _ _  F) as Hf.
  simpl in Hc, Hf.
  pose proof (Continuous_comp I 
            J (toPart theta) (toPart F) mp Hc Hf) as Hcomp.
  exists (fromPart _  ((toPart F)[o](toPart theta)) (fst Hcomp)).
  eapply Continuous_wd; eauto.
  apply toFromPartId.
Defined.




Notation "{ f }" := (getF f).

(** specialize the above the common case where J is [realline].
An advantage is that we get rid of an argument, and thus
reduce the number of non inferable arguments to 2.
This is handy while defining the binary composition notation below *)

Definition composeIContR
  (I : interval) (pI : proper I)
  (F : IContR realline Coq.Init.Logic.I) (theta : IContR I pI)
     : IContR I pI.
  apply (composeIContRGeneral F theta).
  apply maps_compacts_into_strict_imp_weak.
  apply Continuous_imp_maps_compacts_into.
  apply scs_prf.
Defined.

(** ∘ is already taken by MathClasses *)
Notation "F [∘] G" := (composeIContR F G) (at level 100).

Local Definition toR {I : interval}  (ir : RInIntvl I) 
    : RInIntvl realline. 
exists (scs_elem _ _ ir). exact Coq.Init.Logic.I.
Defined.

(* Coercion toRealline : RInIntvl >-> RInIntvl. *)

Lemma composeIContAp : ∀    (I : interval) (pI : proper I)
  (F : IContR realline Coq.Init.Logic.I) (G : IContR I pI) t,
  {F [∘] G} t [=] {F} {|scs_elem := ({G} t) ; scs_prf := Coq.Init.Logic.I |}.
Proof.
  intros ? ? ? ? ?. destruct t. simpl. unfold mkRIntvl. simpl.
  apply TContRExt. simpl.
  apply TContRExt. simpl.
  reflexivity.
Qed.



Definition CSine : IContR realline I.
  exists (fromPart _  Sine (fst Continuous_Sin)).
  eapply Continuous_wd; eauto.
  apply toFromPartId.
  apply Continuous_Sin.
Defined.

Definition CCos : IContR realline I.
  exists (fromPart _  Cosine (fst Continuous_Sin)).
  eapply Continuous_wd; eauto.
  apply toFromPartId.
  apply Continuous_Cos.
Defined.

Definition CFSine 
  (I : interval) (pI : proper I)
  (theta : IContR I pI ) : IContR I pI := (CSine [∘] theta).

Definition CFCos 
  (I : interval) (pI : proper I)
  (theta : IContR I pI ) : IContR I pI := (CCos [∘] theta).


Definition CFAbs
  (I : interval) (pI : proper I)
  (theta : IContR I pI ) : IContR I pI.
  eexists (fromPart _  (FAbs (toPart theta)) _).
Unshelve.
Focus 2.
  simpl. intros ? ?. split; assumption.

  eapply Continuous_wd.
  apply toFromPartId.
  apply Continuous_abs.
  apply scs_prf.
Defined.


Lemma CFAbsAp : ∀  (I : interval) (pI : proper I) (F : IContR I pI ) t,
  {CFAbs F} t [=] AbsIR ({F} t).
Proof.
  intros.
Local Opaque AbsIR.
Local Opaque FAbs. simpl.
  destruct t. simpl.
  rewrite FAbs_char. simpl.
  unfold mkRIntvl. simpl.
  reflexivity.
Qed.

(*
Lemma AbsOfIntegral (itvl : interval) (pI : proper itvl) 
  (a b : RInIntvl itvl) (p: a [<=] b) 
  (F : IContR itvl pI) :
  Cintegral (mkIntBnd p) F [<=] Cintegral (mkIntBnd p) (CFAbs F).
Proof using.
  apply IntegralMonotone.
  intros. rewrite CFAbsAp.
  apply leEq_AbsIR.
Qed.
*)

Lemma AbsOfIntegral (itvl : interval) (pI : proper itvl) 
  (a b : RInIntvl itvl) (p: a [<=] b) 
  (F : IContR itvl pI) :
  AbsIR (Cintegral (mkIntBnd p) F) [<=] Cintegral (mkIntBnd p) (CFAbs F).
Proof using.
  apply AbsSmall_imp_AbsIR.
  split.
- apply inv_cancel_leEq.
  rewrite cg_inv_inv.
  rewrite <- CIntegral_opp.
  apply IntegralMonotone.
  intros. rewrite CFAbsAp. apply inv_leEq_AbsIR.
- apply IntegralMonotone.
  intros. rewrite CFAbsAp.
  apply leEq_AbsIR.
Qed.

Lemma CFAbs_resp_mult (itvl : interval) (pI : proper itvl) 
  (F G : IContR itvl pI) :
  (CFAbs (F[*]G) [=] (CFAbs F) [*] (CFAbs G)).
Proof using.
  apply ExtEqIContR.
  intros. do 1 rewrite IContRMultAp.
  do 3 rewrite CFAbsAp.
  do 1 rewrite IContRMultAp.
  apply AbsIR_resp_mult.
Qed.

Local Opaque Sine.


Lemma CFSineAp : ∀ (I : interval) (pI : proper I) (F : IContR I pI ) t,
  {CFSine F} t [=] Sin ({F} t).
Proof.
  intros. unfold CFSine, composeIContR, composeIContR, CSine. destruct t, F.
  setoid_rewrite  extToPart2. simpl.
  apply pfwdef.
  apply FS_as_CSetoid_proper; try reflexivity.
  simpl. reflexivity.
Qed.
  
Local Opaque Cosine.


Lemma CFCosAp : ∀  (I : interval) (pI : proper I) (F : IContR I pI ) t,
  {CFCos F} t [=] Cos ({F} t).
Proof.
  intros. unfold CFCos. destruct t, F. 
  setoid_rewrite  extToPart2. simpl.
  apply pfwdef.
  apply FS_as_CSetoid_proper; try reflexivity.
  simpl. reflexivity.
Qed.

Hint Rewrite IContRInvAp IContRConstAp CFCosAp CFSineAp IContRPlusAp IContRMultAp IContRMinusAp : IContRApDown.

Require Import IRMisc.IRTrig.

(* TODO : Move to IRMisc.IRTrig *)
Lemma CosineCos : ∀ θ p, Cosine θ p [=] Cos θ.
Proof.
  intros. unfold Cos. simpl. apply pfwdef. reflexivity.
Qed.

Lemma SineSin : ∀ θ p, Sine θ p [=] Sin θ.
Proof.
  intros. unfold Sin. simpl. apply pfwdef. reflexivity.
Qed.

Local Opaque Sin Cos.

Lemma CFCos_minus: ∀ (I : interval) (pI : proper I)  (x y : IContR I pI),
 CFCos (x[-]y)
    [=]CFCos x[*]CFCos y[+]CFSine x[*]CFSine y.
Proof.
  intros ? ? ? ?.
  apply ExtEqIContR.
  intros a.
  autorewrite with IContRApDown.
  apply Cos_minus.
Qed.

Lemma CFSine_minus: ∀ (I : interval) (pI : proper I)  (x y : IContR I pI),
  CFSine (x[-]y)
    [=]CFSine x[*]CFCos y[-]CFCos x[*]CFSine y.
Proof.
  intros ? ? ? ?.
  apply ExtEqIContR.
  intros a.
  autorewrite with IContRApDown.
  apply Sine_minus.
Qed.

Lemma CFCosConst : ∀ (I : interval) (pI : proper I) (θ : IR),
   CFCos (ContConstFun I pI θ) [=] ContConstFun I pI (Cos θ).
Proof.
  intros. apply ExtEqIContR. intros.
  simpl. apply pfwdef. reflexivity.
Qed.

Lemma CFCosSine : ∀ (I : interval) (pI : proper I)  (θ : IR),
   CFSine (ContConstFun I pI θ) [=] ContConstFun I pI (Sin θ).
Proof.
  intros. apply ExtEqIContR. intros.
  simpl. apply pfwdef. reflexivity.
Qed.


Lemma IContRDerivativeComposeGeneral:  ∀ (I J : interval) (pI : proper I) (pJ : proper J)
  (G G' : IContR J pJ) (F F' : IContR I pI)
  (mp: maps_compacts_into I J (toPart F)),
  let mpw := maps_compacts_into_strict_imp_weak I J (toPart F) mp in
  isIDerivativeOf F' F
  → isIDerivativeOf G' G
  → isIDerivativeOf  ((composeIContRGeneral G' F mpw) [*] F') (composeIContRGeneral G  F mpw).
Proof.
  unfold isIDerivativeOf.
  intros.
  eapply Derivative_wdr; [
    apply toPartMultIContR|].
  unfold composeIContR. simpl.
  eapply Derivative_wdl;[apply toFromPartId |].
  eapply Derivative_wdr;[
    apply Feq_mult;[apply toFromPartId | apply Feq_reflexive; apply included_refl]|].
  eapply Derivative_comp; eauto.
Qed.

Lemma IContRDerivativeCompose:  ∀ (I : interval) (pI : proper I) 
  (F F' : IContR I pI) (G G' : IContR realline  Coq.Init.Logic.I),
  isIDerivativeOf F' F
  → isIDerivativeOf G' G
  → isIDerivativeOf  ((G'[∘] F) [*] F') (G [∘] F).
Proof.
  intros. apply IContRDerivativeComposeGeneral; eauto.
Qed.



Lemma IsDerivativeCos : isIDerivativeOf CCos CSine.
Proof.
  unfold isIDerivativeOf, CCos, CSine. simpl.
  eapply Derivative_wdl;[apply toFromPartId |].
  eapply Derivative_wdr;[apply toFromPartId |].
  apply Derivative_Sin.
Qed.

Lemma IsDerivativeSin : isIDerivativeOf ([--]CSine) CCos.
Proof.
  unfold isIDerivativeOf, CCos, CSine. simpl.
  eapply Derivative_wdl;[apply toFromPartId |].
  eapply Derivative_wdr;[apply toPartInv |].
  eapply Derivative_wdr;[apply Feq_inv; apply toFromPartId|].
  apply Derivative_Cos.
Qed.


(** better suited for integration *)
Lemma IsDerivativeSin2 : isIDerivativeOf CSine ([--]CCos).
Proof.
  eapply Derivative_wdr. apply (@IContR_st_eq_Feq realline I).
   apply invInvIContR. 
  apply TContRDerivativeOpp.
  apply IsDerivativeSin.
Qed.

Lemma IContRDerivComposeLinear:  ∀ (I : interval) (pI : proper I) 
   (G G' : IContR realline  Coq.Init.Logic.I) (a b : IR),
   let Fl := (ContConstFun I pI b [+]
            ContConstFun I pI a [*] IContRId I pI) in
  isIDerivativeOf G' G
  → isIDerivativeOf
        ((G'[∘] Fl) [*] (ContConstFun I pI a)) 
        (G [∘] Fl).
Proof.
  intros. apply IContRDerivativeCompose; [| assumption].
  apply TContRDerivativeLinear.
Qed.

(** better suited for integration *)
Lemma IContRDerivComposeLinear2:  ∀  (I : interval) (pI : proper I)
   (G G' : IContR realline  Coq.Init.Logic.I) (a b : IR) (p : a [#] [0]),
   let Fl := (ContConstFun I pI b [+]
            ContConstFun I pI a [*] IContRId I pI) in
  isIDerivativeOf G' G
  → isIDerivativeOf  
        (G'[∘] Fl) 
        ((G [∘] Fl)[*] (ContConstFun I pI (f_rcpcl a p))).
Proof.
  intros  ? ? ? ? ? ? ? ? Hd.
  apply IContRDerivComposeLinear with (pI:=pI) (a:=a) (b:=b) in Hd.
  fold Fl in Hd.
  apply TContRDerivativeMultConstR with (c:=(f_rcpcl a p)) in Hd.
  eapply isIDerivativeOfWdl;[| apply Hd]. clear.
  remember (G' [∘] Fl) as ss.
  clear Heqss. rewrite <- mult_assoc, FConstMult.
  rewrite field_mult_inv.
  fold cr_one. destruct ss. simpl. intros ?. simpl. ring.
Qed.

 
Lemma IContRIntegComposeLinear:  ∀ (I : interval) (pI : proper I) 
   (G G' : IContR realline  Coq.Init.Logic.I) (a b : IR) (p : a [#] [0]) ib,
   let Fl := (ContConstFun I pI b [+]
            ContConstFun I pI a [*] IContRId I pI) in
  isIDerivativeOf G' G
-> Cintegral ib (G' [∘] Fl) 
   [=] (({G[∘] Fl} (intgBndR ib) [-] {G[∘] Fl} (intgBndL ib)) [/]a[//]p).
Proof.
  intros ? ? ? ? ? ? ? ? ? Hd.
  rewrite TBarrowEta;[|apply IContRDerivComposeLinear2 with (p:=p); apply Hd].
  fold Fl. destruct ib. unfold intgBndR, intgBndL. simpl snd. simpl fst.
  unfold cg_minus. remember ((G [∘] Fl)) as gf. clear Heqgf Fl. 
  autorewrite with IContRApDown. unfold cf_div. 
   ring.
Qed.

Lemma IContRIntegLinearCos:  ∀ (I : interval) (pI : proper I) 
   (a b : IR) (p : a [#] [0]) ib,
   let Fl := (ContConstFun I pI b [+]
            ContConstFun I pI a [*] IContRId I pI) in
   Cintegral ib (CCos [∘] Fl) 
   [=] (({CSine [∘] Fl} (intgBndR ib) [-] {CSine[∘] Fl} (intgBndL ib)) [/]a[//]p).
Proof.
  intros. apply IContRIntegComposeLinear.
  apply IsDerivativeCos.
Qed.

Lemma IContRIntegLinearCos2:  ∀ (I : interval) (pI : proper I) 
   (a b : IR) (p : a [#] [0]) ib,
   let Fl := (ContConstFun I pI b [+]
            ContConstFun I pI a [*] IContRId I pI) in
   Cintegral ib (CCos [∘] Fl) 
   [=] ((Sin ({Fl} (intgBndR ib))  [-] Sin ({Fl} (intgBndL ib))) [/]a[//]p).
Proof.
  intros. 
  pose proof (@IContRIntegLinearCos I pI a b p ib) as XX.
  fold Fl in XX. cbv zeta in XX. fold (CFSine Fl) in XX.
  rewrite XX. apply div_wd;[| reflexivity]. clear.
  rewrite CFSineAp, CFSineAp. reflexivity.
Qed.

Lemma IContRIntegLinearSine:  ∀ (I : interval) (pI : proper I) 
   (a b : IR) (p : a [#] [0]) ib,
   let Fl := (ContConstFun I pI b [+]
            ContConstFun I pI a [*] IContRId I pI) in
   Cintegral ib (CSine [∘] Fl) 
   [=] (({([--]CCos) [∘] Fl} (intgBndR ib) [-] {([--]CCos)[∘] Fl} (intgBndL ib)) [/]a[//]p).
Proof.
  intros. apply IContRIntegComposeLinear.
  apply IsDerivativeSin2.
Qed.


Lemma pfwdef2
     : ∀ (S : CSetoid) (F : PartFunct S) (x : S) (Hx : Dom F x) 
       (Hy : Dom F x), F x Hx [=] F x Hy.
Proof.
  intros. apply pfwdef. reflexivity.
Qed.


Lemma IContRIntegLinearSine2:  ∀ (I : interval) (pI : proper I) 
   (a b : IR) (p : a [#] [0]) ib,
   let Fl := (ContConstFun I pI b [+]
            ContConstFun I pI a [*] IContRId I pI) in
   Cintegral ib (CSine [∘] Fl) 
   [=] ((Cos ({Fl} (intgBndL ib))  [-] Cos ({Fl} (intgBndR ib))) [/]a[//]p).
Proof.
  intros. 
  pose proof (@IContRIntegLinearSine I pI a b p ib) as XX.
  fold Fl in XX. cbv zeta in XX.
  rewrite XX. apply div_wd;[| reflexivity]. clear.
  rewrite composeIContAp.
  rewrite composeIContAp. simpl.
  unfold cg_minus. rewrite invInvIR.
  rewrite cag_commutes_unfolded. 
Local Transparent Cos. unfold Cos. simpl. Local Opaque Cos.
  apply csg_op_wd;[apply pfwdef2|].
  apply cg_inv_wd. apply pfwdef2.
Qed.


Lemma IContRDerivativeCos:  ∀ (I : interval) (pI : proper I) 
  (F F' : IContR I pI),
  isIDerivativeOf F' F
  → isIDerivativeOf  ((([--]CSine) [∘] F) [*] F') (CCos [∘] F).
Proof.
  intros. apply IContRDerivativeCompose; auto.
  apply IsDerivativeSin.
Qed.

Lemma TContRDerivativeSin:  ∀ (I : interval) (pI : proper I) 
  (F F' : IContR I pI),
  isIDerivativeOf F' F
  → isIDerivativeOf  (((CCos) [∘] F) [*] F') (CSine [∘] F).
Proof.
  intros. apply IContRDerivativeCompose; auto.
  apply IsDerivativeCos.
Qed.


Hint Rewrite CFCosAp IContRConstAp IContRInvAp CFAbsAp CFSineAp IContRPlusAp IContRMultAp IContRMinusAp IContRIdAp: IContRApDown.
