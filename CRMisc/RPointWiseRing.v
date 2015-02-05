
Require Export CoRN.algebra.CRings.

Section RCSetoid_functions.
Variable S1 : RSetoid.
Variable S2 : CSetoid.


Section unary_functions.

(**
In the following two definitions,
[f] is a function from (the carrier of) [S1] to
(the carrier of) [S2].  *)

Variable f : S1 -> S2.

Definition rfun_wd : Prop :=
     forall x y : S1, x [=] y -> f x [=] f y.

Definition fun_strext : CProp := 
  forall x y : S1, f x [#] f y -> ~ (x [=] y).

Lemma fun_strext_imp_wd : fun_strext -> rfun_wd.
Proof.
 intros H x y H0.
 apply not_ap_imp_eq.
 intro H1.
 generalize (H _ _ H1); intro H2.
 tauto.
Qed.

End unary_functions.

Record RCSetoid_fun : Type :=
  {rcsf_fun    :> S1 -> S2;
   rcsf_strext :  fun_strext rcsf_fun}.

Lemma rcsf_wd : forall f : RCSetoid_fun, rfun_wd f.
Proof.
 intro f.
 apply fun_strext_imp_wd.
 apply rcsf_strext.
Qed.

Lemma rcsf_wd_unfolded: forall (f : RCSetoid_fun) (x y : S1), x[=]y -> f x[=]f y.
Proof rcsf_wd.

Definition Const_RCSetoid_fun : S2 -> RCSetoid_fun.
Proof.
 intro c; apply (Build_RCSetoid_fun (fun x : S1 => c)); intros x y H.
 elim (ap_irreflexive _ _ H).
Defined.

Definition rcap_fun (f g : RCSetoid_fun) :=
  {a : S1 | f a[#]g a}.

Definition req_fun  (f g : RCSetoid_fun) :=
  forall a : S1, f a[=]g a.


Lemma irrefl_apfun :  irreflexive (rcap_fun).
Proof.
 unfold irreflexive in |- *.
 intros f.
 unfold ap_fun in |- *.
 red in |- *.
 intro H.
 elim H.
 intros a H0.
 set (H1 := ap_irreflexive S2 (f a)) in *.
 intuition.
Qed.

Lemma cotrans_apfun : cotransitive (rcap_fun).
Proof.
 unfold cotransitive in |- *.
 unfold ap_fun in |- *.
 intros f g H h.
 elim H.
 clear H.
 intros a H.
 set (H1 := ap_cotransitive S2 (f a) (g a) H (h a)) in *.
 elim H1.
  clear H1.
  intros H1.
  left.
  exists a.
  exact H1.
 clear H1.
 intro H1.
 right.
 exists a.
 exact H1.
Qed.

Lemma ta_apfun : tight_apart (req_fun) (rcap_fun).
Proof.
 unfold tight_apart in |- *.
 unfold ap_fun in |- *.
 unfold eq_fun in |- *.
 intros f g.
 split.
  intros H a.
  red in H.
  apply not_ap_imp_eq.
  red in |- *.
  intros H0.
  apply H.
  exists a.
  exact H0.
 intros H.
 red in |- *.
 intro H1.
 elim H1.
 intros a X.
 set (H2 := eq_imp_not_ap S2 (f a) (g a) (H a) X) in *.
 exact H2.
Qed.

Lemma sym_apfun :  Csymmetric (rcap_fun).
Proof.
 unfold Csymmetric in |- *.
 unfold ap_fun in |- *.
 intros f g H.
 elim H.
 clear H.
 intros a H.
 exists a.
 apply ap_symmetric.
 exact H.
Qed.

Definition RCFS_is_CSetoid :=
  Build_is_CSetoid (RCSetoid_fun) (req_fun) (rcap_fun)
  (irrefl_apfun) (sym_apfun) 
  (cotrans_apfun) (ta_apfun).

Definition RCFS_as_CSetoid :=
  Build_CSetoid (RCSetoid_fun) (req_fun) (rcap_fun)
    (RCFS_is_CSetoid).

End RCSetoid_functions.

Section FunRing.

Variable A : RSetoid.
Variable B : CRing.

Definition FSCSetoid := RCFS_as_CSetoid A B.

Definition FS_sg_op_pointwise : FSCSetoid -> FSCSetoid -> FSCSetoid.
  unfold FSCSetoid. intros f g.
  apply Build_RCSetoid_fun with
    (rcsf_fun := (fun t : A => f t [+] g t)).
  intros ? ? Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep as [Hsep| Hsep];
    [destruct f | destruct g]; auto.
Defined.

Definition FS_sg_op_cs_pointwise : CSetoid_bin_op FSCSetoid.
  apply Build_CSetoid_bin_op with (csbf_fun := FS_sg_op_pointwise).
  intros f1 f2 g1 g2 Hsep.
  simpl in Hsep.
  unfold ap_fun in Hsep.
  destruct Hsep as [a Hsep].
  simpl in Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep;[left|right]; 
  simpl; unfold ap_fun; eexists; eauto.
Defined.

(** There is a [FS_as_CSemiGroup] located at
    [CoRN.algebra.CSemiGroups.FS_as_CSemiGroup]
    It is the semigroup where the operation is
    composition of functions. This semigroup
    is different; it is the poinwise version
    of the operation on B (co-domain) *)

Definition FS_as_PointWise_CSemiGroup : CSemiGroup.
  apply Build_CSemiGroup with (csg_crr := FSCSetoid)
                            (csg_op := FS_sg_op_cs_pointwise).
  unfold is_CSemiGroup.
  unfold associative.
  intros f g h. simpl.
  unfold FS_sg_op_cs_pointwise, FS_sg_op_pointwise, req_fun.
  simpl. eauto  1 with algebra.
Defined.

Definition FS_cm_unit_pw : FSCSetoid :=
  (Const_RCSetoid_fun _ _ [0]).


Definition FS_as_PointWise_CMonoid : CMonoid.
  apply Build_CMonoid with (cm_crr := FS_as_PointWise_CSemiGroup)
                          (cm_unit := FS_cm_unit_pw).
  split; simpl; unfold is_rht_unit; unfold is_rht_unit; 
  intros f; simpl; unfold req_fun; simpl; intros a;
  eauto using cm_rht_unit_unfolded, 
    cm_lft_unit_unfolded.
Defined.

Definition FS_gr_inv_pw : FSCSetoid -> FSCSetoid.
  unfold FSCSetoid. intros f.
  apply Build_RCSetoid_fun with
    (rcsf_fun := (fun t : A =>  [--](f t))).
  intros ? ? Hsep.
  pose proof rcsf_strext as HH.
  unfold fun_strext in HH.
  eauto using csf_strext_unfolded, zero_minus_apart.
Defined.

Definition FS_gr_inv_pw_cs : CSetoid_un_op FSCSetoid.
  apply Build_CSetoid_un_op with (csf_fun := FS_gr_inv_pw).
  intros f1 f2 Hsep. simpl.
  simpl in Hsep.
  unfold ap_fun in Hsep.
  destruct Hsep as [a Hsep].
  simpl in Hsep.
  exists a.
  eauto using zero_minus_apart, 
              minus_ap_zero, csf_strext_unfolded.
Defined.

Definition FS_as_PointWise_CGroup : CGroup.
  apply Build_CGroup with (cg_crr := FS_as_PointWise_CMonoid)
                          (cg_inv := FS_gr_inv_pw_cs).
  split; simpl;
  unfold req_fun;
  unfold FS_sg_op_pointwise, FS_cm_unit_pw, FS_gr_inv_pw;
  simpl; eauto using cg_rht_inv_unfolded,
                     cg_lft_inv_unfolded.
Defined.

Definition FS_as_PointWise_CAbGroup : CAbGroup.
  apply Build_CAbGroup with (cag_crr := FS_as_PointWise_CGroup).
  unfold is_CAbGroup, commutes.
  intros f g. simpl. unfold req_fun.
  simpl. eauto with algebra.
Defined.

Definition FS_mult_pointwise : 
    FSCSetoid -> FSCSetoid -> FSCSetoid.
  unfold FSCSetoid. intros f g.
  apply Build_RCSetoid_fun with
    (rcsf_fun := (fun t : A => f t [*] g t)).
  intros ? ? Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep as [Hsep| Hsep];
    [destruct f | destruct g]; auto.
Defined.

Definition FS_mult_pointwise_cs : CSetoid_bin_op FSCSetoid.
  apply Build_CSetoid_bin_op with (csbf_fun := FS_mult_pointwise).
  intros f1 f2 g1 g2 Hsep.
  simpl in Hsep.
  unfold ap_fun in Hsep.
  destruct Hsep as [a Hsep].
  simpl in Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep;[left|right]; 
  simpl; unfold ap_fun; eexists; eauto.
Defined.

Definition FS_cg_one_pw : FSCSetoid :=
  (Const_RCSetoid_fun _ _ [1]).

Lemma FS_mult_pointwise_assoc 
  : associative FS_mult_pointwise.
 unfold associative.
  intros f g h a. simpl.
  eauto  1 with algebra.
Defined.

(** To prove that the unit of multiplication
    is not the same as the unit of addition,
    ,i.e. [1] [#] [0], i.e. [ax_non_triv],
    [A] must be non-empty.
    Otherwise the extensional equality on 
    function space means that
    [fun _ => [0]] [=] [fun _ => [1]]
*)

Variable aa : A.

Definition FS_as_PointWise_CRing : CRing.
  apply Build_CRing with (cr_crr := FS_as_PointWise_CAbGroup)
                         (cr_mult := FS_mult_pointwise_cs)
                         (cr_one := FS_cg_one_pw).
  apply Build_is_CRing 
    with (ax_mult_assoc := FS_mult_pointwise_assoc);
  simpl.
- split; simpl; unfold is_rht_unit; unfold is_rht_unit; 
  intros f; simpl; unfold req_fun; simpl; intros a;
  eauto using mult_one, one_mult.
- intros f g a. simpl. apply mult_commut_unfolded.
- intros f g h a. simpl. apply  ring_dist_unfolded.
- unfold ap_fun. exists aa. simpl.
  apply ring_non_triv.
Defined.

End FunRing.

Require Import Coq.Classes.Morphisms.

(** TODO : Pull request to the file where [FS_as_CSetoid] is defined *)
Instance FS_as_CSetoid_proper : forall A B, 
  Proper (@st_eq  (FS_as_CSetoid A B) ==> @st_eq A ==> @st_eq B) 
         (fun f g => f g).
Proof.
  intros ? ? f g Hf x y Ha.
  rewrite Ha.
  apply Hf.
Qed.

