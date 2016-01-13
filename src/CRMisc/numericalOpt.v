Require Import IRLemmasAsCR.
Require Import MathClasses.implementations.bool.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.rings.
Require Import MathClasses.theory.rings.

Section Opt.
(** we need to often compare reals. This can
 -only be done upto a finte (but arbitrary) accuracy.*)
Variable eps : Qpos.
 
(* Move *)
Definition approxDecLtRQ (a:CR) (b:Q) : bool :=
let aq : Q := approximate a eps in
bool_decide (aq + eps < b).


(* Move *) 
Lemma approxDecLtRQSound: forall (a:CR) (b:Q),
approxDecLtRQ a b = true
-> a < 'b.
Proof using.
  intros ? ? H.
  apply bool_decide_true in H.
  eapply le_lt_trans;
    [apply upper_CRapproximation with (e:=eps)|].
  apply (@strictly_order_preserving _ _ _ _ _  _ _ _).
  exact H.
Qed.

(* Move *)
Lemma approxDecLtRQApproxComplete: forall (a:CR) (b:Q),
a < '(b - 2*`eps)
-> approxDecLtRQ a b = true.
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
Definition approxDecLtRR (a b :CR) : bool :=
approxDecLtRQ (a-b) (0)%mc.


(* Move *) 
Lemma approxDecLtRRSound: forall (a b:CR),
approxDecLtRR a b = true
-> a < b.
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

(* Move *)
Lemma approxDecLtRRApproxComplete: forall (a b:CR),
a < b - '(2*`eps)
-> approxDecLtRR a b = true.
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

End Opt.