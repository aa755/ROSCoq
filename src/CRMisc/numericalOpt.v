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

Definition objectiveApprox (a:A) : Q := approximate (objective a) eps.


Let betterMax (a b : A) : bool :=
  bool_decide ((objectiveApprox a) < (objectiveApprox b)).

(** find the element of the list that approximately maximizes
the objective. As we will show next, the suboptimality is at most [2*eps]. *)
Definition approxMaximize :(list A) -> option A:=
conditionalOptimize condition betterMax.

(* Move *)
Lemma filter_app :
  forall f (l1 l2 : list A),
    filter f (l1 ++ l2) ≡ filter f l1 ++ filter f l2.
Proof using.
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

Require Import Qminmax.

(* Move *)
Locate decide.
Require Import MathClasses.misc.decision.

(** the latter is more convenient, as it safes a step of interpreting boolean
values *)
Lemma bool_decide_sumbool `{Decision P} {T:Type} : forall (a b : T),
(if (bool_decide P) then  a  else b) ≡ 
(if (decide P) then a else b).
Proof using.
  intros ? ?.
  destruct (decide P) as [p|p].
- apply bool_decide_true in p; rewrite p. reflexivity. 
- apply bool_decide_false in p; rewrite p. reflexivity. 
Qed.

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
  → In m l.
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
  destruct (condition a); auto;[].
  simpl in H.
  destruct
  ((fold_right (λ (y : A) (x : option A), chooseOp betterMax x y) None
         (filter condition l))); unfold chooseOp in H; simpl in H; 
         [|inversion H; auto; fail].
  unfold choose in H.
  destruct (betterMax a a0); inversion H; subst; auto.
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
  dands; auto;[].
  eapply approxMaximizeMax; eauto.
Qed.

  
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

End conditionalOpt.


End Opt.