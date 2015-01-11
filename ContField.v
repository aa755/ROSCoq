
Require Export CoRN.ftc.MoreIntervals.
Require Export PointWiseRing.

Set Implicit Arguments.

Section ContFAlgebra.
Variable itvl : interval.

Definition RInIntvl := Build_SubCSetoid IR (itvl).

Definition mkRIntvl (r : IR) (p : (itvl) r) : RInIntvl := 
  (Build_subcsetoid_crr  _ _ r p).

Definition RI_R := FS_as_SemiGroup RInIntvl IR.


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


Lemma extToPart (f : RI_R) : forall (x:IR) (p : (itvl) x) 
  (p' : Dom (toPart f) x), f (mkRIntvl x p) [=] (toPart f) x p'.
Proof.
  intros ? ? ?.
  destruct f. unfold toPart. simpl.
  simpl in p'.
  unfold fun_strext in csf_strext.
  apply not_ap_imp_eq.
  intros Hc.
  apply csf_strext in Hc.
  simpl in Hc.
  revert Hc.
  apply eq_imp_not_ap.
  apply eq_reflexive.
Qed.

Lemma extToPartLt (f : RI_R) : forall (x y:IR) (px : (itvl) x) (py : (itvl) y)
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
    -> (toPart f) x (scs_prf _ _ x) [<] (toPart f) y (scs_prf  _ _ y).
Proof.
  intros. destruct x,y. eapply extToPartLt; eauto.
Qed.

Lemma extToPart2 (f : RI_R) : forall (x:IR) (p : (itvl) x),
  f (mkRIntvl x p) [=] (toPart f) x p.
Proof.
  intros ? ?.
  destruct f. unfold toPart. simpl.
  unfold fun_strext in csf_strext.
  apply not_ap_imp_eq.
  intros Hc.
  apply csf_strext in Hc.
  simpl in Hc.
  revert Hc.
  apply eq_imp_not_ap.
  apply eq_reflexive.
Qed.


Lemma extToPart3 (f : RI_R) : forall (t : RInIntvl),
  (f  t) [=] (toPart f) t (scs_prf _ _ t).
Proof.
  intros ?.
  destruct t.
  simpl.
  apply extToPart2.
Qed.

Definition IContR := Build_SubCSetoid RI_R
    (fun f => Continuous itvl (toPart f)).

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

Lemma IContRCont_I : ∀ (f : IContR) (l r : RInIntvl) (p : l[<=]r), 
    Continuous_I p (toPart f).
Proof.
  intros ? ? ? ?.
  pose proof (IContRCont f l r) as Hc.
  unfold Continuous in Hc.
  apply Hc.
  unfold compact, iprop.
  apply included_refl.
Defined.

Lemma TMin_LeEq_Max : ∀ a b : RInIntvl , TMin a b[<=] TMax a b.
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

Variable pItvl : proper itvl.

Definition isIDerivativeOf (F' F : IContR) : CProp :=
  Derivative _ pItvl (toPart F) (toPart F').

Lemma TContRExt : forall (f : IContR) a b,
  a [=] b -> {f} a [=] {f} b.
Proof.
  intros ? ? ? H.
  unfold getF. rewrite H.
  apply eq_reflexive.
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

