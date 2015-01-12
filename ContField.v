
Require Export CoRN.ftc.MoreIntervals.
Require Export PointWiseRing.

Set Implicit Arguments.

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


Notation "{ f }" := (getF f).

(* Continuous_Sin Continuous_com *)
Require Export CoRN.transc.Trigonometric.

Definition CFSine (theta : IContR) : IContR.
  pose proof (scs_prf _ _  theta) as Hc.
  simpl in Hc.
  pose proof (fun mw => Continuous_comp itvl 
            realline (toPart theta) Sine mw Hc) as Hcomp.
  apply Continuous_imp_maps_compacts_into in Hc.
  apply maps_compacts_into_strict_imp_weak in Hc.
  specialize (Hcomp Hc Continuous_Sin).
  exists (fromPart (Sine[o]toPart theta) (fst Hcomp)).
  eapply Continuous_wd; eauto.
  apply toFromPartId.
Defined.

Definition CFCos (theta : IContR) : IContR.
  pose proof (scs_prf _ _  theta) as Hc.
  simpl in Hc.
  pose proof (fun mw => Continuous_comp itvl 
            realline (toPart theta) Cosine mw Hc) as Hcomp.
  apply Continuous_imp_maps_compacts_into in Hc.
  apply maps_compacts_into_strict_imp_weak in Hc.
  specialize (Hcomp Hc Continuous_Cos).
  exists (fromPart (Cosine[o]toPart theta) (fst Hcomp)).
  eapply Continuous_wd; eauto.
  apply toFromPartId.
Defined.

Require Import Coq.Unicode.Utf8.

Require Import CoRNMisc.
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

Hint Resolve (scs_prf IR (itvl)) : CoRN.

Definition TMin (ta tb :RInIntvl) : RInIntvl:= 
  {|
    scs_elem := Min ta tb;
    scs_prf := interval_Min (scs_prf _ _ ta) (scs_prf _ _ tb) |}.

Definition TMax (ta tb :RInIntvl) : RInIntvl:= 
  {|
    scs_elem := Max ta tb;
    scs_prf := interval_Max (scs_prf _ _ ta) (scs_prf _ _ tb) |}.

Lemma intvlIncluded : forall (ta tb : RInIntvl),
  included (clcr ta tb) (itvl).
Proof.
  destruct ta as [ra pa].
  destruct tb as [rb pb].
  simpl. apply interval_convex; trivial.
Defined.


Lemma IContRCont : forall (tf : IContR) (ta tb : RInIntvl), 
    Continuous  (clcr ta tb) (toPart tf).
Proof.
  intros ? ? ?.
  pose proof (scs_prf _ _ tf) as Hc.
  simpl in Hc.
  eapply Included_imp_Continuous; eauto.
  apply intvlIncluded.
Defined.

Lemma IContRCont_I : ∀ (f : IContR) (l r : RInIntvl) 
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


Definition CIntegral (l r : RInIntvl) (f : IContR) : IR :=
  Integral (IContRCont_IMinMax f l r).


Definition isIDerivativeOf (F' F : IContR) : CProp :=
  Derivative _ pItvl (toPart F) (toPart F').

Lemma TContRExt : forall (f : IContR) a b,
  a [=] b -> {f} a [=] {f} b.
Proof.
  intro f. apply  csf_fun_wd.
Qed.


Lemma TBarrow : forall (F F': IContR)
         (der : isIDerivativeOf F' F) (a b : RInIntvl),
       CIntegral a b F' [=] {F} b [-] {F} a.
Proof.
  intros ? ? ? ? ?.
  unfold getF,  CIntegral.
  pose proof (Barrow _ _ (scs_prf _ _ F') pItvl _ der a b 
      (IContRCont_IMinMax _ _ _) (scs_prf _ _ a) (scs_prf _ _ b)) as Hb.
  simpl in Hb.
  rewrite TContRExt with (b:=b) in Hb by (destruct b; simpl; reflexivity).
  remember ({F} b) as hide.
  rewrite TContRExt with (b:=a) in Hb by (destruct a; simpl; reflexivity).
  subst hide.
  rewrite <- Hb. apply Integral_wd'; reflexivity.
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

