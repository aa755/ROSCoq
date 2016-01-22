 Require Import IRLemmasAsCR.
Require Import MathClasses.implementations.bool.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.rings.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.option.
Require Import StdlibMisc.



Section conditionalOpt.
(** we need to often compare reals. This can
 -only be done upto a finte (but arbitrary) accuracy.*)
Variable eps : Qpos.

Variable A:Type.
Variable condition : A → bool.
Variable objective : A → CR.

Definition objectiveApprox (a:A) : Q := approximate (objective a) eps.


Let betterMax (a b : A) : bool :=
  bool_decide ((objectiveApprox a) < (objectiveApprox b)).

(** find the element of the list that approximately maximizes
the objective. As we will show next, the suboptimality is at most [2*eps]. *)
Definition approxMaximize :(list A) -> option A:=
conditionalOptimize condition betterMax.


Require Import Qminmax.

Require Import MCMisc.decInstances.

Require Import MathClasses.misc.decision.
Require Import Psatz.
Lemma objectiveApproxChoose : forall (a b: A),
objectiveApprox (choose betterMax a b) =
Qminmax.Qmax (objectiveApprox a) (objectiveApprox b).
Proof using.
  intros ? ?.
  unfold choose, betterMax.
  rewrite bool_decide_sumbool.
  destruct (decide (objectiveApprox a < objectiveApprox b)) as [l|l];
  [rewrite Q.max_r|rewrite Q.max_l]; try reflexivity.
  - apply Qlt_le_weak; assumption.
  - autounfold with QMC in l. lra.
Qed.  


Lemma approxMaximizeSome : ∀  (l: list A ) (m: A) ,
  approxMaximize l ≡ Some m 
  → In m l /\ condition m = true.
Proof using.
  intros ? ?. unfold approxMaximize, conditionalOptimize.
  rewrite <- fold_left_rev_right.
  rewrite in_rev.
  rewrite <- rev_filter.
  remember (rev l) as ll.
  revert m. clear dependent l.
  rename ll into l.
  induction l; unfold approxMaximize, conditionalOptimize
   ; intro ; simpl; intro H ; auto;[discriminate|].
  remember (condition a) as ca.
  destruct ca;[|apply IHl in H; tauto].
  simpl in H.
  destruct
  ((fold_right (λ (y : A) (x : option A), chooseOp betterMax x y) None
         (filter condition l))); unfold chooseOp in H; simpl in H; 
         [|inversion H; subst; auto; fail].
 unfold choose in H.
  destruct (betterMax a a0); inversion H; subst; auto;
    [apply IHl in H; tauto].
Qed.
  
Lemma approxMaximizeMaxQ : ∀ (c:A) (l: list A ) (m: A) ,
  condition c = true
  → In c l
  → approxMaximize l ≡ Some m 
  → objectiveApprox c  ≤ (objectiveApprox m).
Proof using.
  unfold approxMaximize, conditionalOptimize.
  intros ? ? ?.
  rewrite <- fold_left_rev_right.
  rewrite in_rev.
  rewrite <- rev_filter.
  remember (rev l) as ll.
  clear dependent l.
  rename ll into l.
  revert m.
  induction l; intros ? h1 h2; simpl in *;[contradiction|].
  destruct h2.
- subst. rewrite h1. clear IHl.
  intro Hc.
  destruct l; simpl in *.
  + unfold chooseOp in Hc. inversion Hc. reflexivity.
  + unfold chooseOp in Hc. inversion Hc.
    clear.
    destruct
     (fold_right
        (λ (y : A) (x : option A),
         Some match x with
              | Some b' => choose betterMax y b'
              | None => y
              end) None
        (if condition a then a :: filter condition l else filter condition l));
    simpl;[| reflexivity].
    rewrite objectiveApproxChoose.
    apply Q.le_max_l.
- remember (condition a) as ca.
  destruct ca; [|dands; eauto; fail].
  symmetry in Heqca.
(** c is inside the tail of the list, 
    and the condition is true for the head of the list *)
  simpl. intro Hc.
  remember (fold_right (λ (y : A) (x : option A), chooseOp betterMax x y) None
           (filter condition l)) as ama.
  destruct ama.
  Focus 2.
    assert (In c (filter condition l)) as Hin by (apply filter_In; auto).
    destruct (filter condition l); simpl in *;[contradiction|].
    inversion Heqama; fail.
  
  symmetry in Heqama.
  rewrite <- (rev_involutive l) in Heqama.
  rewrite  rev_filter in Heqama.
  rewrite fold_left_rev_right in Heqama.
  apply approxMaximizeSome in Heqama.
  unfold  chooseOp at 1  in Hc.
  unfold choose, betterMax in Hc.
  rewrite bool_decide_sumbool in Hc.
  destruct (decide (objectiveApprox a < objectiveApprox a0)); inversion Hc.
  + setoid_rewrite H1 in IHl.
    apply IHl; auto.
  + autounfold with QMC in n.
    assert (objectiveApprox a0 <= objectiveApprox a)%Q as ht by lra.
    subst.
    eapply transitivity;[| apply ht].
    apply IHl; auto.
Qed.

(* Move *)
Lemma approximateLe : forall (a b : CR),
approximate a eps ≤ approximate b eps
→ a - ' (2 * ` eps) ≤ b.
Proof using.
  intros ? ? H.
  eapply transitivity;
    [|apply lower_CRapproximation with (e:=eps)].
  apply flip_le_minus_l.
  eapply transitivity;
    [apply upper_CRapproximation with (e:=eps)|].
  fold ((@cast Q (st_car (msp_is_setoid CR)) inject_Q_CR)).
  rewrite <- (@preserves_plus Q CR _ _ _ _ _ _ _ _ _ _ _ _ _ ).
  apply (@order_preserving _ _ _ _ _ _ _ _ _ _).
  simpl.
  autounfold with QMC in *.
  remember (approximate a eps).
  remember (approximate b eps).
  destruct eps.
  simpl in *.
  lra.
Qed.

Lemma approxMaximizeMax : ∀ (c:A) (l: list A ) (m: A) ,
  condition c = true
  → In c l
  → approxMaximize l ≡ Some m 
  → objective c - '(2*`eps)  ≤ (objective m).
Proof using.
  intros ? ? ? h1 h2 h3.
  eapply approxMaximizeMaxQ in h3; eauto.
  unfold objectiveApprox in h3.
  apply approximateLe.
  assumption.
Qed.

Lemma approxMaximizeSomeIf : ∀ (c : A) (l: list A ) ,
  condition c = true
  → In c l
  → ∃ (m : A),  approxMaximize l ≡ Some m.
Proof using.
  intros ? ?.
  unfold approxMaximize, conditionalOptimize.
  rewrite <- fold_left_rev_right.
  rewrite in_rev.
  rewrite <- rev_filter.
  remember (rev l) as ll.
  clear dependent l.
  rename ll into l.
  intros Hc Hi.
  assert (In c (filter condition l)) as Hin by (apply filter_In; auto).
  destruct (filter condition l); simpl in Hin; auto;[contradiction|].
  simpl.
  eexists. reflexivity.
Qed.

Lemma approxMaximizeCorrect : ∀ (c : A) (l: list A ) ,
  condition c = true
  → In c l
  → ∃ (m : A),
      In m l
      ∧ condition m = true
      ∧ approxMaximize l ≡ Some m
      ∧ objective c - '(2*`eps)  ≤ (objective m).
Proof using.
  intros ? ? Hc Hi.
  pose proof Hc as Hcbb.
  eapply approxMaximizeSomeIf in Hc; eauto.
  destruct Hc as [m Hc].
  exists m.
  pose proof Hc as Hcb.
  apply approxMaximizeSome in Hcb.
  repnd.
  dands; auto;[].
  eapply approxMaximizeMax; eauto.
Qed.

End conditionalOpt.
