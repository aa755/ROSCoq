 Require Import IRLemmasAsCR.
Require Import MathClasses.implementations.bool.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.rings.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.option.
Require Import StdlibMisc.
Require Import MCMisc.bisectionSearch.
Require Import Psatz.

(* unline CoRN.reals.fast.CRArith.CR_epsilon_sign_dec, 
  this needs only one approximation *)
Definition CR_eps_sign_dec (ε:Qpos) (c:CR) : Datatypes.comparison:=
let ap := approximate c ε in
if (Qlt_le_dec ap (- ε))%Q then Datatypes.Lt
else if (Qlt_le_dec ε ap)%Q then Datatypes.Gt
else Eq.

Require Import LibTactics.
Open Scope mc_scope.

Lemma CR_eps_sign_decLt : forall ε c,
CR_eps_sign_dec ε c ≡ Datatypes.Lt
-> (c < 0).
Proof.
  intros ? ? H. unfold CR_eps_sign_dec in H.
  cases_if; inverts H as H;[| cases_if; inverts H].
  assert ((approximate c ε + ε < 0)%Q) as Hh by lra.
  clear H0.
  pose proof (upper_CRapproximation c ε) as Ht.
  apply CRlt_Qlt in Hh.
  eapply le_lt_trans;[apply Ht|].
  apply CR_lt_ltT. assumption.
Qed.

Lemma CR_eps_sign_decGt : forall ε c,
CR_eps_sign_dec ε c ≡ Datatypes.Gt
-> (0 < c).
Proof.
  intros ? ? H. unfold CR_eps_sign_dec in H.
  cases_if; inverts H as H.
  cases_if; inverts H as H.
  assert ((0 < approximate c ε - ε)%Q) as Hh by lra.
  clear H0 H1.
  pose proof (lower_CRapproximation c ε) as Ht.
  apply CRlt_Qlt in Hh.
  eapply lt_le_trans;[|apply Ht].
  apply CR_lt_ltT. assumption.
Qed.


Section QBisect.
Require Import QArith.

Definition bisectQ (a b:Q) : Q := ((Qmake 1 2) * (a + b))%Q.
Variable f : Q -> CR.
Variable desired : CR.
Variable ε : Qpos.

(* the direction that the search should continue if [f] is an increasing function *)
Let incDirection (q:Q) : Datatypes.comparison := CR_eps_sign_dec ε (desired - (f q)).
Let decDirection (q:Q) : Datatypes.comparison := CR_eps_sign_dec ε ((f q) - desired).

Definition solveIncQ :=
 bisectionSearch bisectQ incDirection.

Definition solveDecQ :=
 bisectionSearch bisectQ decDirection.


End QBisect.

(* arcsin result is correct. sine of 30 degrees is half *)
Example arcsinApprox : 
  let ans := solveIncQ rational_sin (' Qmake 1 2) (QposMake 1 100) (0,Qmake 3 2) 100 in
  Datatypes.option_map (Basics.compose approximateAngleAsDegrees (cast Q CR)) ans 
  = (Some 30%Z) .
Proof.
  vm_compute.
  reflexivity.
Abort.


(* violation of monotonocity. so the search fails*)
Example arcsinApprox : 
  let ans := solveDecQ rational_sin (' Qmake 1 2) (QposMake 1 100) (0,1) 100 in
  Datatypes.option_map (Basics.compose approximateAngleAsDegrees (cast Q CR)) ans 
  = None .
Proof.
  vm_compute.
  reflexivity.
Abort.


(* arcsin result is correct. cos of 60 degrees is half *)
Example arccosApprox : 
  let ans := solveDecQ rational_cos (' Qmake 1 2) (QposMake 1 100) (0,Qmake 3 2) 100 in
  Datatypes.option_map (approximateAngleAsDegrees ∘ (cast Q CR)) ans 
  = (Some 60%Z) .
Proof.
  vm_compute.
  reflexivity.
Abort.

(* violation of monotonocity. so the search fails*)
Example arccosApprox : 
  let ans := solveIncQ rational_cos (' Qmake 1 2) (QposMake 1 100) (0,Qmake 3 2) 100 in
  Datatypes.option_map (approximateAngleAsDegrees ∘ (cast Q CR)) ans 
  = None .
Proof.
  vm_compute.
  reflexivity.
Abort.

Section CRBisect.
  Variable f : CR -> CR.
  Variable desired : CR.
  Variable ε : Qpos.
  Let fq : Q -> CR := f ∘ (cast Q CR).
  Variable sr : CR * CR.
  Let srq := ((approximate (fst sr) ε + ε), (approximate (snd sr) ε) - `ε).
  
Definition solveIncCR : nat → option Q :=
  solveIncQ fq desired ε srq.

Definition solveDecCR :=
  solveDecQ fq desired ε srq.

End CRBisect.

(* arcsin result is correct. sine of 30 degrees is half *)
Example arcsinApprox : 
  let ans := solveIncCR sin (' Qmake 1 2) (QposMake 1 100) ('0,'Qmake 3 2) 100 in
  Datatypes.option_map (Basics.compose approximateAngleAsDegrees (cast Q CR)) ans 
  = (Some 30%Z) .
Proof.
  vm_compute.
  reflexivity.
Abort.


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
