
Require Export CoRN.ftc.MoreIntervals.
Require Export PointWiseRing.

Set Implicit Arguments.
Require Import Coq.Unicode.Utf8.

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


Require Import CoRNMisc.

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

Definition CIntegral (l r : RInIntvl) (f : IContR) : IR :=
  Integral (IContRCont_IMinMax f l r).

Definition Cintegral {l r : RInIntvl}  (p : l [<=] r) (f : IContR) : IR :=
  integral _ _ _ _ (IContRCont_I f p).

Instance CIntegral_wd : Proper 
    ((@st_eq RInIntvl) 
      ==> (@st_eq RInIntvl) 
      ==> (@st_eq IContR) ==> (@st_eq IR)) CIntegral.
Proof.
  intros la lb Hl ra rb Hr f g Hfg.
  unfold CIntegral.
  pose proof (Integral_wd' _ _ _ _ 
    (IContRCont_IMinMax f la ra) _ _ _ (IContRCont_IMinMax f lb rb)) as HH.
  simpl in HH. destruct la,lb,ra,rb. simpl in HH, Hl, Hr. simpl.
  specialize (HH Hl Hr).
  rewrite HH.
  apply Integral_wd.
  pose proof (@st_eq_Feq_included f g) as Hst.
  match goal with
  [ |- Feq (Compact ?vc) _ _] => match type of vc with
                                 CSetoids.scs_elem _ _ ?a [<=] CSetoids.scs_elem _ _ ?b =>  
                                    specialize (Hst a b)
                                 end
  end.
  simpl in Hst. apply Hst. destruct f, g. trivial.
Qed.

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

Add Ring IRisaRing: (CRing_Ring IContR).

Lemma lb_CIntegral:
  ∀ (a b : RInIntvl) (F : IContR) (c : RInIntvl),
  (∀ x : RInIntvl, (clcr a b) x → c[<=] {F} x)
  → c[*](b[-]a)[<=]CIntegral a b F.
Proof.
  intros ? ? ? ? Hle.
  unfold CIntegral.
  rewrite HIntegral



Section CIntegralArith.
Variable (a b : RInIntvl).
Variable (F G : IContR).

Lemma CIntegral_plus : 
   CIntegral a b (F [+] G) [=] CIntegral a b F [+] CIntegral a b G.
Proof.
  unfold CIntegral.
  erewrite <- Integral_plus; eauto.
  apply Integral_wd.
  apply Feq_symmetric.
  eapply included_Feq;[|apply toPartSum]; eauto.
  apply includeMinMaxIntvl.
  Grab Existential Variables.
  eapply Continuous_I_wd.
  eapply included_Feq.
  Focus 2. apply Feq_symmetric. apply toPartSum; fail.
              apply includeMinMaxIntvl; fail.
  eapply included_imp_Continuous. apply (scs_prf _ _ (F [+]G)).
  apply includeMinMaxIntvl.
Qed.
End CIntegralArith.



Section CIntegralProps.
Variable (a b : RInIntvl).
Variable (F G : IContR).

Lemma IntegralMonotone : 
   (forall (r: RInIntvl), (clcr (TMin a b) (TMax a b) r) -> {F} r[<=] {G} r)
   -> CIntegral a b F [<=] CIntegral a b G.
Proof.
  intros Hle.
  pose proof (CIntegral_plus a b F (F [+] (G [-] F))) as Hp.
  assert (F [+] (G [-] F) [=] G) as Heq by (unfold cg_minus; ring).
  rewrite <- Heq. clear Heq.
  rewrite CIntegral_plus.
  apply shift_leEq_plus'.
  rewrite cg_minus_correct.
  apply equal_less_leEq with (a:= Min a b) (b:= Max a b);[| |apply Min_leEq_Max].
- intros Hmm. apply Min_less_Max_imp_ap in Hmm.
  apply 

  

  match goal with
  [|- [<=]
  pose proof (equal_less_leEq _ a b [0] CIntegral a b (G[-]F)).

  apply leEq_def.
  intros Hc.
  

Abort.

Lemma IntegralMonotone : 
  (forall r Hf Hg, 
        (clcr (Min a b) (Max a b) r) -> F r Hf[<=] G r Hg)
   ->Integral contF [<=] Integral contG.
Proof.
  intros  Hb.
  pose proof (Continuous_I_minus _ _ Hab _ _ contG contF)
     as Hc.
  pose proof (Integral_plus _ _ Hab _ _ contF Hc).
  
Abort.


End ContFAlgebra.

(*
Definition ContFSG : CSemiGroup.

Definition ContFMonoid : CMonoid.

Definition ContFGroup : CGroup.

Definition ContFAbGroup : CAbGroup.

Definition ContFRing : CRing.

Definition ContField : CField.
*)

