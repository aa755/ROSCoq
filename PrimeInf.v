(** Based on proof submitted by Ilmārs Cīrulis to coq-club on 
      1/26/2015 *)

Require Import PArith Psatz.

Definition divide n m := exists k, n * k = m.
Definition is_prime n := 1 < n /\ (forall m, 1 < m -> divide m n -> m = n).

(* Theorem divider_gt m n: 0 < n -> n < m -> divide m n -> False.
Proof.
 intros. destruct H1.
 abstract( destruct x; [| rewrite mult_succ_r in H1; set (W := m * x); fold W in H1 ]; omega ).
Qed. *)

Open Scope positive.

Theorem pos_lt_wf_rec n (P: positive -> Set): (forall n0, (forall m, (m < n0) -> P m) -> P n0) -> P n.
Proof.
 set (H := fun n (P: positive -> Set)
  (F: forall n, (forall m, lt (Pos.to_nat m) (Pos.to_nat n) -> P m) -> P n)
  => Arith.Wf_nat.induction_ltof2 positive Pos.to_nat P F n).
 intros. apply (H n P). intros.
 apply H0. intros. apply H1. abstract lia.
Defined.
Definition compare_dec n m := ZArith_dec.Dcompare_inf (n ?= m).
Definition pos_lt_eq_lt_dec n m: { n < m } + { m = n } + { m < n }.
Proof.
 destruct (compare_dec n m). destruct s.
  apply Pos.compare_eq_iff in e. auto.
  rewrite Pos.compare_lt_iff in e. auto.
  apply Pos.compare_gt_iff in e. auto.
Defined.
Definition pos_lt_dec n m: { n < m } + { m <= n }.
Proof.
 destruct (compare_dec n m). destruct s.
  apply Pos.compare_eq_iff in e. right. rewrite e. apply Pos.le_refl.
  rewrite Pos.compare_lt_iff in e. auto.
  apply Pos.compare_gt_iff in e. right. abstract lia.
Defined.

Theorem divider_le n m: (n | m) -> (n ?= m <> Gt).
Proof. intros ? ?. destruct H. apply Pos.compare_gt_iff in H0. abstract nia. Qed.

Definition pos_divide_dec m n: { (m | n) } + { ~ (m | n) }.
Proof.
 pattern n; apply pos_lt_wf_rec; clear n; intros.
 destruct (pos_lt_eq_lt_dec m n0). destruct s.
  pose (Pos.sub_decr _ _ l). destruct (H _ l0).
   left. destruct d. exists (x + 1).
    rewrite Pos.mul_add_distr_r, Pos.mul_1_l, <- H0, Pos.sub_add; auto.
   right. intro. apply n. destruct H0. exists (x - 1).
    rewrite Pos.mul_sub_distr_r, Pos.mul_1_l, <- H0; auto. abstract nia.
  left. inversion e. exists 1. rewrite Pos.mul_1_l. auto.
  right. intro. destruct H0. abstract nia.
Defined.

Theorem divide_trans a b c: (a | b) -> (b | c) -> (a | c).
Proof.
 intros. destruct H, H0. exists (x * x0).
 rewrite H0, H, Pos.mul_assoc, (Pos.mul_comm x0). auto.
Qed.

Fixpoint list_product L :=
 match L with
 | nil => 1
 | cons n l => list_product l * n
 end.

Theorem prod_thm_0 L k: List.In k L -> (k | list_product L).
Proof.
 intro. induction L.
  inversion H.
  simpl in *. destruct H.
   exists (list_product L). rewrite H. auto.
   destruct (IHL H). exists (x * a). abstract nia.
Qed.

Theorem prod_thm_1 L k: List.In k L -> k <= list_product L. (* fact_thm_2 *)
Proof.
 intro. induction L.
  inversion H.
  simpl in *. destruct H.
   abstract nia.
   apply IHL in H. abstract nia.
Qed.

Definition pos_prime n := 1 < n /\ (forall m, 1 < m -> (m | n) -> m = n).

Definition first_divisor_dec n x:
  { m | 1 < m < x /\ (m | n) } + { forall m, 1 < m < x -> (m | n) -> False }.
Proof.
 apply (Pos.peano_rect (fun x => { m | 1 < m < x /\ (m | n) } + { forall m, 1 < m < x -> (m | n) -> False })).
  right. intros. abstract lia.
  intros. destruct H.
   left. destruct s. exists x0. destruct a. split. abstract lia. auto.
   destruct (pos_divide_dec p n).
    destruct (pos_lt_dec 1 p).
     left. exists p. split. split. auto. abstract lia. auto.
     right. intros. abstract lia.
    right. intros. destruct (pos_lt_dec m p).
     elim (f m); auto. destruct H. auto.
     assert (p = m) by abstract lia. rewrite H1 in n0. exact (n0 H0).
Defined.

Theorem prime_thm n (H: 1 < n): (forall m, 1 < m < n -> (m | n) -> False) <-> pos_prime n.
Proof.
 split; intros.
  split; auto. intros. destruct (pos_lt_dec m n).
   exfalso. apply (H0 m). auto. auto. destruct H2. abstract nia.
   destruct H0, H1. assert (m = n) by auto. destruct H2. abstract nia.
Qed.

Theorem not_prime_thm n (H: 1 < n): { m | 1 < m < n /\ (m | n) } -> ~ pos_prime n.
Proof.
 intro. intro. destruct H0. destruct a. destruct H1. destruct H0. pose (H3 x H0 H2). abstract lia.
Qed.
Theorem not_prime_thm' n (H: 1 < n): ~ pos_prime n -> { m | 1 < m < n /\ (m | n) }.
Proof.
 intro. rewrite <- prime_thm in H0. destruct (first_divisor_dec n n).
  destruct s. destruct a. exists x. auto.
  elim (H0 f). auto.
Defined.

Definition prime_dec n: { pos_prime n } + { ~ pos_prime n }.
Proof.
 destruct (pos_lt_dec n 2).
  right. intro. destruct H. abstract lia.
  destruct (first_divisor_dec n n).
   right. destruct s. apply not_prime_thm. abstract lia. eauto.
   left. apply prime_thm; auto. abstract lia.
Defined.

Theorem prime_divisor n: 1 < n -> { p | pos_prime p /\ (p | n) }.
Proof.
 pattern n; apply pos_lt_wf_rec; clear n; intros.
 destruct (prime_dec n0).
  exists n0. split; auto. exists 1. rewrite Pos.mul_1_l. auto.
  apply not_prime_thm' in n. destruct n. destruct a. destruct (prime_dec x).
   eauto.
   destruct H1. pose (H x H3 H1). destruct s. destruct a.
    exists x0. split; auto. eapply divide_trans; eauto. auto.
Defined.

Require Export Coq.Lists.List.
Notation " [] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..).
Notation  π₁ := projT1.
Notation  "ℕ⁺" := positive.
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "∃ x   , P" := (sigT (fun x => P)) (at level 10).
Notation "x ∧ y" := (prod x  y) (at level 90, right associativity) : type_scope.

Notation "p ∉ L" := (~ (In p L)) (at level 80, right associativity).
Notation isPrime := pos_prime.


Theorem prime_infinitude : ∀ (L : list ℕ⁺), 
      ∃ p , (p ∉ L ∧ isPrime p).
Proof.
  intros L.
  set (P := list_product L). pose (prod_thm_0 L).
  assert (forall k, 1 < k -> List.In k L -> ~ (k | P + 1)).
  intros. apply d in H0. intro. destruct H0, H1. fold P in H0.
  assert (x0 = x + 1) by abstract nia. abstract nia.
 assert (1 < P + 1) by abstract lia. destruct (prime_divisor _ H0). destruct a.
 assert (~ List.In x L). intro. destruct H1. exact (H x H1 H3 H2).
 eauto.
Defined.

(*
Eval compute in 
  ( π₁ (prime_infinitude [2,3,5,7])). *)