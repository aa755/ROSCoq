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
  max::
    (List.map 
        (mult max) 
        (equiMidPoints (Z.to_pos numSamples))).

Require Import MathClasses.misc.decision.
Require Import MathClasses.implementations.stdlib_binary_integers.

Definition qroundClosest (q:Q) : Z :=
let quotRem := ((Z.quotrem (Qnum q) (Qden q))) in
let quot := fst quotRem in
let rem := snd quotRem in
if ((rem  <? '(Qden q) - rem ))%Z
then quot else quot + 1.


Lemma equiSpacedSamplesCorrect (q:Q) :
0 ≤ q ≤ max -> {qs : Q | (List.In qs equiSpacedSamples) 
                      /\ abs (qs - q) ≤ (1 # 2) * ` δ}.
Proof.
  intros.
  exists (let ns := (Z.to_pos numSamples) in
          Qmake (qroundClosest (q * (Qmake 1 ns))) ns).
Abort.  
  
End sampling.
