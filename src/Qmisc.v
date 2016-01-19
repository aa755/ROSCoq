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
  unfold equiSpacedSamples.
  unfold equiMidPoints.
  remember (Pos.to_nat (Z.to_pos numSamples)) as nn.
  destruct nn; simpl.
- remember numSamples as ns.
  destruct ns; simpl in Heqnn; try discriminate.
  symmetry in Heqnn.
  apply (P.nat_of_P_nonzero p) in Heqnn. contradiction.  

- remember numSamples as ns.
  destruct ns;  simpl in Heqnn; try discriminate.
  + unfold numSamples in Heqns.
    pose proof (Q.Zle_Qle_Qceiling (max / δ) 0) as H.
    apply proj1 in H.
    rewrite <- Heqns in H.
    inversion Heqnn. subst. simpl. 
    exists max. split;[auto|].
    lapply H;[clear H; intro H| compute; intro xx; discriminate].
    apply Q.Qle_shift_div_r in H;[| auto].
    setoid_rewrite preserves_0 in H.
    setoid_rewrite (mult_0_l) in H.
    destruct δ.
    autounfold with QMC in *. simpl in *. lra.

  + simpl. unfold firstNPos. simpl. (*2 cases, based on whether p is greater that 1 *)
   admit.
  + (** exact same as the first cas *)
    unfold numSamples in Heqns.
    pose proof (Q.Zle_Qle_Qceiling (max / δ) 0) as H.
    apply proj1 in H.
    rewrite <- Heqns in H.
    inversion Heqnn. subst. simpl. 
    exists max. split;[auto|].
    lapply H;[clear H; intro H| compute; intro xx; discriminate].
    apply Q.Qle_shift_div_r in H;[| auto].
    setoid_rewrite preserves_0 in H.
    setoid_rewrite (mult_0_l) in H.
    destruct δ.
    autounfold with QMC in *. simpl in *. lra.
Abort.

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
