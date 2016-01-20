Require Import CoRN.model.structures.Qpossec.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.rings.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.implementations.stdlib_rationals.


Section sampling.
Variable δ: Qpos.
Variable max : Q.

(** the goal here is to create a list of rationals
between 0 and [max] such that any point in that range
is at most δ/2 away from some member of the list.*)



(* In OCaml, one can start from 0 and keep adding δ until maxValidAngleApprox
is reached. It is hard to convince Coq 
that that function is terminating. 
*)

Definition numSamples : Z := Qround.Qceiling  (max / δ).

Lemma Zto_pos_le : forall x,
(cast Z Q x) ≤ ((Z.to_pos x):Q).
Proof using.
  intros.
  destruct x; simpl; auto;
  compute; intro; discriminate.
Qed.

Lemma numSamplesLe : 
  max*(Qmake 1 (Z.to_pos numSamples)) ≤ δ.
Proof using.
  remember (Z.to_pos numSamples) as zp.
  change ((1 # zp)%Q) with (Qinv zp).
  apply (Qmult_le_r _ _ zp);[auto|].
  unfold mult, recip, Q_mult.
  field_simplify;[| auto].
  rewrite Q.Qdiv_1_r.
  rewrite Q.Qdiv_1_r.
  subst zp.
  unfold numSamples.
  apply (Qmult_le_r _ _ (Qinv δ));[apply Qpossec.Qpos_inv_obligation_1|].
  field_simplify;[| auto| auto].
  rewrite Q.Qdiv_1_r.
  SearchAbout Z.to_pos Qle.
  remember ((max / δ)%Q).
  eapply transitivity;[| apply Zto_pos_le].
  apply Qround.Qle_ceiling.
Qed.

Require Import StdlibMisc.
Definition equiSpacedSamples : list Q :=
    (List.map 
        (mult max) 
        (equiMidPoints (Z.to_pos numSamples))) ++ [max].

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.additional_operations.
Require Import MathClasses.theory.rings.

Hint Unfold pow stdlib_rationals.Q_Npow plus
  one zero stdlib_rationals.Q_1 stdlib_rationals.Q_plus
  stdlib_binary_naturals.N_plus
  stdlib_binary_naturals.N_1
  equiv stdlib_rationals.Q_eq mult
  stdlib_rationals.Q_mult dec_recip
  stdlib_rationals.Q_recip
  zero stdlib_rationals.Q_0
  le stdlib_rationals.Q_le
  lt stdlib_rationals.Q_lt
  canonical_names.negate stdlib_rationals.Q_opp  : QMC.

    Require Import Psatz.

Lemma  equiSpacedSamplesFst: 
  {q :Q | List.head  equiSpacedSamples ≡ Some q /\ q ≤ δ }.
Proof.
  unfold equiSpacedSamples, equiMidPoints, numSamples.
  pose proof (Qlt_le_dec 1 (max / δ)) as Hd.
  destruct Hd.
- pose proof q as qb.
  apply Qlt_not_le in q.
  setoid_rewrite <- Q.Zle_Qle_Qceiling in q.
  rewrite Z.nle_gt in q.
  pose proof q as qrb.
  remember ((Qround.Qceiling (max / δ))) as ns.
  rewrite Heqns in qrb.
  destruct ns; simpl in *;
  try omega;[| inversion q; fail].
  apply P.Plt_lt in q.
  change (Pos.to_nat 1) with (1%nat) in q.
  remember (Pos.to_nat p) as n.
  destruct n;[omega|].
  destruct n;[omega|].
  simpl. eexists. split;[reflexivity|].
  apply Z2Pos.inj_iff in Heqns; [|  eauto with *| omega].
  rewrite Pos2Z.id in Heqns.
  rewrite Heqns.
  apply numSamplesLe.

- pose proof q as qb. apply Q.Zle_Qle_Qceiling in q.
  apply Q.Qle_shift_div_r in qb;[| auto];
  setoid_rewrite (mult_1_l) in qb.
  exists max.
  destruct (Qround.Qceiling (max / δ)); simpl in *;
    try (split; auto).
  apply Z.Ple_Zle, P.Ple_le in q.
  change (Pos.to_nat 1) with (1%nat) in q.
  remember (Pos.to_nat p) as n.
  destruct n;[|destruct n;[| omega]]; simpl; reflexivity.
Qed.

(* proof is almost same as above. delete the above version as it is not useful *)
Lemma  equiSpacedSamplesFst2:
0 ≤ max 
-> {q :Q | List.head  equiSpacedSamples ≡ Some q /\ 0 ≤ q ≤ δ }.
Proof.
  intro H.
  unfold equiSpacedSamples, equiMidPoints, numSamples.
  pose proof (Qlt_le_dec 1 (max / δ)) as Hd.
  destruct Hd.
- pose proof q as qb.
  apply Qlt_not_le in q.
  setoid_rewrite <- Q.Zle_Qle_Qceiling in q.
  rewrite Z.nle_gt in q.
  pose proof q as qrb.
  remember ((Qround.Qceiling (max / δ))) as ns.
  rewrite Heqns in qrb.
  destruct ns; simpl in *;
  try omega;[| inversion q; fail].
  apply P.Plt_lt in q.
  change (Pos.to_nat 1) with (1%nat) in q.
  remember (Pos.to_nat p) as n.
  destruct n;[omega|].
  destruct n;[omega|].
  simpl. eexists. split;[reflexivity|].
  apply Z2Pos.inj_iff in Heqns; [|  eauto with *| omega].
  rewrite Pos2Z.id in Heqns.
  rewrite Heqns.
  split;[|apply numSamplesLe].
  autounfold with QMC in *.
  apply nonneg_mult_compat;[assumption|].
  apply (Qinv_le_0_compat (Z.to_pos (Qround.Qceiling (max / δ)))).
  compute.
  intro XXX; discriminate.

- pose proof q as qb. apply Q.Zle_Qle_Qceiling in q.
  apply Q.Qle_shift_div_r in qb;[| auto];
  setoid_rewrite (mult_1_l) in qb.
  exists max.
  destruct (Qround.Qceiling (max / δ)); simpl in *;
    try (split; auto).
  apply Z.Ple_Zle, P.Ple_le in q.
  change (Pos.to_nat 1) with (1%nat) in q.
  remember (Pos.to_nat p) as n.
  destruct n;[|destruct n;[| omega]]; simpl; reflexivity.
Qed.

Require Import MathClasses.misc.decision.
Require Import MathClasses.implementations.stdlib_binary_integers.

Definition qroundClosest (q:Q) : Z :=
let quotRem := ((Z.quotrem (Qnum q) (Qden q))) in
let quot := fst quotRem in
let rem := snd quotRem in
if ((rem  <? '(Qden q) - rem ))%Z
then quot else quot + 1.

(** can be strengthened to replace [` δ] by [(1 # 2) * ` δ] *)
Lemma equiSpacedSamplesCorrect (q:Q) :
0 ≤ q ≤ max -> {qs : Q | (List.In qs equiSpacedSamples) 
                      /\ abs (qs - q) ≤ (1 # 2) * ` δ}.
Proof.
  intros.
  exists (let ns := (Z.to_pos numSamples) in
          Qmake (qroundClosest (q * (Qmake 1 ns))) ns).
Abort.  
  
End sampling.
