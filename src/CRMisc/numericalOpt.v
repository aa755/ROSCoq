Require Import IRLemmasAsCR.
Require Import MathClasses.implementations.bool.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.rings.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.option.
Require Import StdlibMisc.

Section Opt.
(** we need to often compare reals. This can
 -only be done upto a finte (but arbitrary) accuracy.*)
Variable eps : Qpos.
 
Definition approxDecLtRQ (a:CR) (b:Q) : bool :=
let aq : Q := approximate a eps in
bool_decide (aq + eps < b).


Lemma approxDecLtRQSound: forall (a:CR) (b:Q),
approxDecLtRQ a b = true
→ a < 'b.
Proof using.
  intros ? ? H.
  apply bool_decide_true in H.
  eapply le_lt_trans;
    [apply upper_CRapproximation with (e:=eps)|].
  apply (@strictly_order_preserving _ _ _ _ _  _ _ _).
  exact H.
Qed.

Lemma approxDecLtRQApproxComplete: forall (a:CR) (b:Q),
a < '(b - 2*`eps)
→ approxDecLtRQ a b = true.
Proof using.
  intros ? ? H.
  apply bool_decide_true.
  rewrite preserves_minus in H.
  apply flip_lt_minus_l  in H.
  rewrite negate_involutive in H.
  apply (@strictly_order_reflecting _ _ _ _ _
      _ (@cast Q CR _) _).
  eapply le_lt_trans;[| apply H]. clear H.
  apply flip_le_minus_l.
  eapply transitivity;
    [|apply lower_CRapproximation with (e:=eps)].
  rewrite <- (@preserves_minus Q _ _ _ _ _ _ _ 
        CR _ _ _ _ _ _ _ _ _).
  apply (@order_preserving _ _ _ _ _
      _ (@cast Q CR _) _).
  apply eq_le. 
  autounfold with QMC.
  destruct eps. simpl.
  ring.
Qed.

(* Move *)
Global Instance  stableBoolEq : ∀ (a b : bool),
MathClasses.misc.util.Stable (a = b).
Proof using.
  intros ? ? H.
  unfold DN in H.
  destruct a; destruct b; try auto;  try tauto.
  - setoid_rewrite not_false_iff_true in H. tauto.
  - setoid_rewrite not_true_iff_false in H. tauto.
Qed.

Require Import CoRN.logic.Stability.

Lemma CRNotLeLtDN : forall (a b : CR),
not (a < b)
-> util.DN (b ≤ a).
Proof.
  intros ? ? Hl Hd.
  pose proof (CRle_lt_dec b a) as Hdn.
  apply Hdn. intro Hdd. clear Hdn.
  destruct Hdd;[tauto|].
  apply CR_lt_ltT in c.
  tauto.
Qed.
  
Lemma approxDecLtRQApproxFalse: forall (a:CR) (b:Q),
approxDecLtRQ a b = false
→ '(b - 2*`eps) ≤ a .
Proof using.
  intros ? ? H.
  apply stable.
  apply not_true_iff_false in H.
  apply CRNotLeLtDN.
  intro Hc.
  apply H. 
  apply approxDecLtRQApproxComplete.
  assumption.
Qed.

Definition approxDecLtRR (a b :CR) : bool :=
approxDecLtRQ (a-b) (0)%mc.


Lemma approxDecLtRRSound: forall (a b:CR),
approxDecLtRR a b = true
→ a < b.
Proof using.
  intros ? ?.
  unfold approxDecLtRR.
  intro H.
  apply approxDecLtRQSound in H.
  rewrite (@preserves_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _) in H.
  apply flip_lt_minus_l in H.
  rewrite plus_0_l in H.
  exact H.
Qed.

Lemma approxDecLtRRApproxComplete: forall (a b:CR),
a < b - '(2*`eps)
→ approxDecLtRR a b = true.
Proof using.
  intros ? ? H.
  apply approxDecLtRQApproxComplete.
  apply flip_lt_minus_l.
  rewrite preserves_minus.
  rewrite preserves_0.
  rewrite plus_0_l.
  rewrite (@commutativity _ _ _ plus _ _ _).
  exact H.
Qed.

Lemma approxDecLtRRApproxFalse: forall (a b:CR),
approxDecLtRR a b = false
→ b - '(2*`eps)  ≤ a.
Proof using.
  intros ? ? H.
  apply approxDecLtRQApproxFalse in H.
  rewrite preserves_minus in H.
  rewrite preserves_0 in H.
  rewrite plus_0_l in H.
  apply flip_le_minus_r in H.
  rewrite (@commutativity _ _ _ plus _ _ _) in H.
  exact H.
Qed.


Section conditionalOpt.
Variable A:Type.
Variable condition : A → bool.
Variable objective : A → CR.

Let betterMax (a b : A) : bool :=
  (approxDecLtRR (objective a) (objective b)).

(** find the element of the list that approximately maximizes
the objective. As we will show next, the suboptimality is at most [2*eps]. *)
Definition approxMaximize :(list A) -> option A:=
conditionalOptimize condition betterMax.

(* Move *)
Lemma filter_app :
  forall f (l1 l2 : list A),
    filter f (l1 ++ l2) ≡ filter f l1 ++ filter f l2.
Proof.
  induction l1; simpl; auto. intro.
  rewrite IHl1.
  destruct (f a); auto.
Qed.

(* Move *)
Lemma rev_filter : forall (f: A -> bool) (l:list A),
filter f (rev l) ≡ rev (filter f l).
Proof using.
  induction l; auto; []; simpl.
  rewrite filter_app.
  simpl. rewrite IHl.
  destruct (f a); auto.
  rewrite app_nil_r.
  reflexivity.
Qed.



Lemma approxMaximizeCorrect : ∀ (c : A) (l: list A ) ,
  condition c = true
  → In c l
  → ∃ (m : A),
      In m l
      ∧ approxMaximize l ≡ Some m 
      ∧ objective c - '(2*`eps)  ≤ (objective m).
Proof.
  unfold approxMaximize, conditionalOptimize.
  intros ? ?.
  rewrite <- fold_left_rev_right.
  rewrite in_rev.
  setoid_rewrite in_rev at 2.
  rewrite <- rev_filter.
  remember (rev l) as ll.
  clear dependent l.
  rename ll into l.
  induction l; intros h1 h2; simpl in *;[contradiction|].
  unfold approxMaximize, conditionalOptimize. simpl.
  destruct h2.
- subst. rewrite h1.
  simpl. unfold chooseOp at 2. simpl. 
  admit. 
- specialize (IHl h1 H). destruct IHl as [mr Hmr1].
  repnd.
  destruct (condition a);[|exists mr; dands; try tauto].
 exists (choose betterMax a mr). simpl.
  rewrite Hmr1rl.
  unfold  chooseOp, choose. unfold betterMax.
  remember (approxDecLtRR (objective a) (objective mr)) as comp.
  fold betterMax.
  destruct comp;[tauto|].
  dands; auto.
  eapply transitivity;[exact Hmr1rr|].
  symmetry in Heqcomp.
  apply stable.
  intro Hc.
  apply not_true_iff_false in Heqcomp.
  apply Heqcomp.
  clear Heqcomp.
  fold (@bool_eq).
  fold (@canonical_names.equiv bool _).
  apply stable.
  pose proof (CRle_lt_dec (objective mr) (objective a)) as Hdn.
  SearchAbout DN.
  Locate DN.
Require Import CoRN.logic.Stability.
  eapply DN_fmap;[exact Hdn|].
  intro Hd.
  destruct Hd;[tauto|].
  apply approxDecLtRRApproxComplete.
  apply CR_lt_ltT.
(** This is clearly unprovable. because the comparison between
reals is inexact, errors can add up, and the suboptimality can grow
upto  [2* eps * (length l)].

As a counter example, consider an increasing list where the difference
between successive elements approaches [2* eps] from below.
The algorithm is free to choose the first element as the maximum.

Hence while folding the list, the EXACT
maximum of the objective value has to be maintained, and the comparison
has to be done w.r.t that value. Then, it should be possible to prove 
a suboptimality of [2*eps].

Perhaps keep this version for now, just in case the new version is too slow.
One can always divide [eps] by the length of the list.
It is not clear which strategy is better.
Run on some examples for Mazda 3.
*)

Abort.

Lemma CRapproxMax : forall (a b : CR),
(approximate (CRmax a b) eps)
  = QMinMax.Qmax (approximate a ((1 # 2) * eps)%Qpos)
  (approximate b ((1 # 2) * eps)%Qpos).
Proof using.
  intros ? ?. reflexivity.
Qed.

(** can this be faster in some cases? *)
Definition CRmax' (a b : CR) : CR :=
match (CR_epsilon_sign_dec eps (b-a)) with
| Datatypes.Gt => b
| Datatypes.Lt => a
| Datatypes.Eq => CRmax a b
end.

Definition approxMaxIter (r: option (A * CR)) (a:A) : option (A * CR) :=
Some 
(
let oa := objective a in 
match r with
| None => (a,oa)
| Some r' => 
    if (approxDecLtRR (snd r') oa) 
    then (a,oa)
    else (fst r', CRmax (snd r') (objective a))
end).

(** find the element of the list that approximately maximizes
the objective. As we will show next, the suboptimality is at most [2*eps]. *)
Definition approxMax (l:list A) : option (A * CR) :=
let l := filter condition l in
fold_left approxMaxIter l None.

Require Import fastReals.interface.

Require Import Qminmax.

(* Move*)
Definition maxListIter `{MaxClass AA} (oa: option AA) (a: AA) : option AA :=
Some
(match oa with
| None => a
| Some a' => max a a'
end).

(* Move*)
Definition maxList `{MaxClass AA} (l: list AA) : option AA :=
fold_left maxListIter l None.

Lemma approxMaximizeCorrect : ∀ (c : A) (l: list A ) ,
  condition c = true
  → In c l
  → ∃ (m : A) (mr: CR),
      In m l
      ∧ approxMax l ≡ Some (m, mr)
      ∧ objective m ≤ mr 
      ∧ objective c - '(2*`eps)  ≤ (objective m).
Proof.
  unfold approxMax.
  intros ? ?.
  rewrite <- fold_left_rev_right.
  rewrite in_rev.
  setoid_rewrite in_rev at 2.
  rewrite <- rev_filter.
  remember (rev l) as ll.
  clear dependent l.
  rename ll into l.
  induction l; intros h1 h2; simpl in *;[contradiction|].
  unfold approxMaximize, conditionalOptimize. simpl.
  destruct h2.
- 
  (**[c] was the first element *)
  subst. rewrite h1. clear IHl.
  simpl. 
  match goal with 
  [|- context [fold_right ?a ?b ?v ]] => remember (fold_right a b v) as ama
  end.
  destruct ama as [ama | ]; simpl.
  + clear Heqama.
    unfold approxMaxIter.
    remember (approxDecLtRR (snd ama) (objective c)).
    setoid_rewrite <- Heqb. destruct b.
    * 
    (** the objective at [c] was observed to be larger that the elements in the tail*)
      exists c. exists (objective c).
      dands; try tauto;[reflexivity|].
      admit. (*easy*)
    * exists (fst ama).
      exists ((CRmax (snd ama)) (objective c)).
      SearchAbout approximate.
      assert (objective (fst ama)  ≤ snd ama) by admit.
      dands; try auto.
      admit. (* prove a separate lemma *)
      
      eapply transitivity; eauto. apply  CRmax_ub_l; fail.
      
      apply stable. apply CRNotLeLtDN.
      intro Hc.
      
      symmetry in Heqb.
      apply approxDecLtRRApproxFalse in Heqb.
      remember (approxDecLtRR (objective (fst ama)) (objective c)) as bb.
      symmetry in Heqbb.
      destruct bb.
      
      apply  approxDecLtRRSound in Heqbb.
      assert ( objective (fst ama) < snd ama).
        eapply lt_le_trans. apply Hc.  apply Heqb. 
      clear H. clear Hc.

      admit.
      admit. (* need to generalize the induction over c*)
  + exists c. exists (objective c).
    dands; try tauto;[reflexivity|].
    admit. (*easy*)
- specialize (IHl h1 H). destruct IHl as [mr IHl].
  destruct IHl as [mrr Hmr1].
  repnd.
  destruct (condition a);[|exists mr; exists mrr; dands; tauto].
  exists (if (approxDecLtRR mrr (objective a)) then a else mr). simpl.
  exists (if (approxDecLtRR mrr (objective a)) then (objective a) 
      else (CRmax mrr (objective a))).
  rewrite Hmr1rl.
  unfold approxMaxIter.
  simpl snd.
  remember ( approxDecLtRR mrr (objective a) ) as comp.
  symmetry in Heqcomp.
  destruct comp.
  +  apply approxDecLtRRSound in Heqcomp.
   dands;  try tauto;[reflexivity|].
   apply lt_le in Heqcomp. unfold PropHolds in Heqcomp.
   eapply transitivity; eauto.
  + dands; auto;[].
    eapply transitivity;[exact Hmr1rrl|].
    apply CRmax_ub_l.
Abort.


End conditionalOpt.


End Opt.