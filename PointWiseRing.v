
Require Export CoRN.algebra.CRings.
Section FunRing.

Variable A : CSetoid.
Variable B : CRing.

Definition FSCSetoid := FS_as_CSetoid A B.
Hint Resolve (@csf_strext FSCSetoid) : CoRN.

Definition FS_sg_op : FSCSetoid -> FSCSetoid -> FSCSetoid.
  unfold FSCSetoid. intros f g.
  apply Build_CSetoid_fun with
    (csf_fun := (fun t : A => f t [+] g t)).
  intros ? ? Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep as [Hsep| Hsep];
    [destruct f | destruct g]; auto.
Defined.

Definition FS_sg_op_cs : CSetoid_bin_op FSCSetoid.
  apply Build_CSetoid_bin_op with (csbf_fun := FS_sg_op).
  intros f1 f2 g1 g2 Hsep.
  simpl in Hsep.
  unfold ap_fun in Hsep.
  destruct Hsep as [a Hsep].
  simpl in Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep;[left|right]; 
  simpl; unfold ap_fun; eexists; eauto.
Defined.

Definition FS_as_SemiGroup : CSemiGroup.
  apply Build_CSemiGroup with (csg_crr := FSCSetoid)
                            (csg_op := FS_sg_op_cs).
  unfold is_CSemiGroup.
  unfold associative.
  intros f g h. simpl.
  unfold FS_sg_op_cs, FS_sg_op, eq_fun.
  simpl. intros a. apply plus_assoc_unfolded.
Defined.


End FunRing.



