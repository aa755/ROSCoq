
Require Export CoRN.ftc.MoreIntervals.

Set Implicit Arguments.

Section ContFAlgebra.
Variable itvl : interval.

Definition RInIntvl := Build_SubCSetoid IR (itvl).

Definition mkRIntvl (r : IR) (p : (itvl) r) : RInIntvl := 
  (Build_subcsetoid_crr  _ _ r p).

Definition RI_R := FS_as_CSetoid RInIntvl IR.


Definition toPart (f : RI_R) : PartIR.
  destruct f.
  apply Build_PartFunct with (pfdom := (itvl)) 
    (pfpfun := fun ir pp => csf_fun (mkRIntvl ir pp)).
  - apply iprop_wd.
  - unfold fun_strext in csf_strext. intros ? ? ? ?. apply csf_strext.
Defined.

(*
Definition fromPart (f : PartIR) : RI_R.
  destruct f. unfold RI_R.
  simpl. apply Build_CSetoid_fun with 
    (csf_fun := fun x=> pfpfun (scs_elem _ _ x) (scs_prf _ _ x)).
*)

Lemma extToPart (f : RI_R) : forall (x:IR) (p : (itvl) x) 
  (p' : Dom (toPart f) x), f (mkRIntvl x p') [=] (toPart f) x p'.
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

Definition IContR := Build_SubCSetoid RI_R
    (fun f => Continuous itvl (toPart f)).


End ContFAlgebra.
  
(*
Definition ContFSG : CSemiGroup.

Definition ContFMonoid : CMonoid.

Definition ContFGroup : CGroup.

Definition ContFAbGroup : CAbGroup.

Definition ContFRing : CRing.

Definition ContField : CField.
*)

