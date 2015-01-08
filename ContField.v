
Require Export CoRN.ftc.MoreIntervals.

Set Implicit Arguments.

Section ContFAlgebra.
Variable itvl : interval.

Definition RInIntvl := Build_SubCSetoid IR (itvl).

Definition mkRIntvl (r : IR) (p : (itvl) r) : RInIntvl := 
  (Build_subcsetoid_crr  _ _ r p).

Definition RI_R := FS_as_CSetoid RInIntvl IR.


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

End ContFAlgebra.

(*
Definition ContFSG : CSemiGroup.

Definition ContFMonoid : CMonoid.

Definition ContFGroup : CGroup.

Definition ContFAbGroup : CAbGroup.

Definition ContFRing : CRing.

Definition ContField : CField.
*)

