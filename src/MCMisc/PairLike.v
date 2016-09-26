(** For better readability, one often constructs
  custom records with semantically aptly named projections
  instead of using the standard pair type.
  For example, consider Vector.Cart2D.

  However, it is tedious to redo common constructions, e.g.
  rings with pointwise operations,
  for each such record type constructor.
   This typeclass is an attempt to
  do such constructions generically once and forall.
 *)
Set Implicit Arguments.
Class PairLike {C A B : Type}
  (mkPair : A -> B -> C)
  (fst : C -> A)
  (snd : C -> B) := 
{
  pairLikeFst : forall  (a:A) (b:B),
    fst (mkPair a b) = a;
  pairLikeSnd : forall  (a:A) (b:B),
    snd (mkPair a b) = b
}.

Section ForgetTypeclassInstances.
Require Import MathClasses.interfaces.canonical_names.
Instance CastPairLikeSame 
`{@PairLike Pair A A mkpair pfst psnd} : Cast A Pair :=
  fun p => mkpair p p.

Instance EquivPairLike 
`{@PairLike Pair A B mkpair pfst psnd}
`{Equiv A} `{Equiv B} 
  : Equiv (Pair) := 
  fun a b => pfst a = pfst b /\ psnd a = psnd b.

Instance EquivalencePairLike 
`{@PairLike Pair A B mkpair pfst psnd}
`{Equiv A} `{Equiv B}
  `{Equivalence _ (@equiv A _)} `{Equivalence _ (@equiv B _)} 
    : Equivalence (@equiv (Pair) _).
Proof.
  split.
- intros x.  split; auto with *.
- intros x y.  intros Hd; destruct Hd;
      split; auto with relations.

- intros x y z. intros h0 h1.
    destruct h0, h1. simpl in *.
    split; eauto 10
    with relations; simpl.
Qed.

Instance ProperPairLikeFst 
`{@PairLike Pair A B mkpair pfst psnd}
{_ : Equiv A} {_: Equiv B} :
     Proper  (equiv ==> equiv) pfst.
Proof.
  intros a b Heq. destruct Heq; assumption.
Qed.

Instance ProperPairLikeSnd 
`{@PairLike Pair A B mkpair pfst psnd}
`{Equiv A} `{Equiv B} :
     Proper  (equiv ==> equiv) psnd.
Proof.
  intros a b Heq. destruct Heq; assumption.
Qed.


Require Export MathClasses.theory.rings.
Require Export MathClasses.interfaces.abstract_algebra.
Instance ZeroPairLike
`{@PairLike Pair A B mkpair pfst psnd}
 `{Zero A} `{Zero B} 
    : Zero (Pair)
    := mkpair 0 0.


Instance OnePairLike 
`{@PairLike Pair A B mkpair pfst psnd}
 `{One A} `{One B}
    : One (Pair)
    := mkpair 1 1.

Instance PlusPairLike 
`{@PairLike Pair A B mkpair pfst psnd}
`{Plus A} `{Plus B} 
    : Plus (Pair)
    := λ a b, mkpair (pfst a + pfst b) (psnd a + psnd b).

Instance MultPairLike
`{@PairLike Pair A B mkpair pfst psnd}
 `{Mult A} `{Mult B} 
    : Mult (Pair)
    := λ a b, mkpair (pfst a * pfst b) (psnd a * psnd b).

Instance NegatePairLike
`{@PairLike Pair A B mkpair pfst psnd}
 `{Negate A} `{Negate B} 
    : Negate (Pair)
    := λ a , mkpair (-(pfst a)) (-(psnd a)).

Section PairLikeRing.
Context `{@PairLike Pair A B mkpair pfst psnd}.

Context `{Ring A}.
Context `{Ring B}.


Add Ring  tempA : (rings.stdlib_ring_theory A).
Add Ring  tempB : (rings.stdlib_ring_theory B).

Require Import Ring.
Typeclasses eauto :=3.

Instance RingPairLike : Ring Pair.
Typeclasses eauto :=30.

Proof.
  repeat(split);
  (repeat match goal with
  | [ H: equiv _ _ |- _ ] => 
      destruct H
  end);
  simpl; subst; eauto 4 with relations;
  compute;
  repeat rewrite (@pairLikeFst _ _ _ mkpair pfst psnd);
  repeat rewrite (@pairLikeSnd _ _ _ mkpair pfst psnd);
  fold (@equiv A _);
  fold (@plus A _);
  fold (@mult A _);
  fold (@zero A _);
  fold (@one A _);
  fold (@negate A _);
  fold (@equiv B _);
  fold (@plus B _);
  fold (@mult B _); 
  fold (@zero B _);
  fold (@one B _);
  fold (@negate B _);
  subst;
  try ring; try assumption;
  (repeat match goal with
  | [ H: equiv _ _ |- _ ] => 
      repeat rewrite H; clear H
  end); try ring; try assumption.
Qed.


End PairLikeRing.


Instance ProperCastPairLikeSame 
`{@PairLike Pair A A mkpair pfst psnd}
`{Equiv A}:
    Proper (equiv ==> equiv) (cast  A (Pair)).
Proof.
    intros ? ? ?. split; compute; 
    [repeat rewrite pairLikeFst| repeat rewrite pairLikeSnd];
    assumption.
Qed.

Instance ProperPairLikeMkpair
`{@PairLike Pair A B mkpair pfst psnd}
`{Equiv A}
`{Equiv B}:
  Proper (equiv ==> equiv  ==> equiv) (mkpair).
Proof.
  intros ? ? h1  ? ? h2. split; simpl;
   repeat rewrite pairLikeFst; repeat rewrite pairLikeSnd;
  assumption.
Qed.

Lemma foldPlusPairLike 
`{@PairLike Pair A B mkpair pfst psnd}
`{Ring A}
`{Ring B} : forall xa xb ya yb,
  mkpair (xa + xb) (ya + yb) = mkpair (xa) (ya)
    + mkpair (xb) (yb).
Proof.
    intros. split; compute;
   repeat rewrite pairLikeFst; repeat rewrite pairLikeSnd;
   reflexivity.
Qed.

Instance pair_instance_le 
`{@PairLike Pair A B mkpair pfst psnd}
`{Le A}
`{Le B}
: Le (Pair) :=
  λ p1 p2, (pfst p1 ≤ pfst p2) ∧ (psnd p1 ≤ psnd p2).

(*
Instahce : SFmap Rigid2DState :=
fun _ _ f c => {|pos2D := sfmap f (pos2D c); θ2D := f (θ2D c)|}.
*)

Require Import StdlibMisc.

Instance LePairPreorder
`{@PairLike Pair A B mkpair pfst psnd}
{la: Le A}
{lb: Le B}
{_: @PreOrder A la}
{_: @PreOrder B lb}
  : PreOrder (pair_instance_le).
Proof.
  split; intros ?; unfold le, pair_instance_le;
  eauto with relations.
  intros. repnd. eauto with relations.
Qed.

Require Import MathClasses.interfaces.orders.

Instance LePairPartialOrder
`{@PairLike Pair A B mkpair pfst psnd}
`{Ring A}  `{Ring B}
`{Le A}
`{Le B}
`{@PartialOrder A _ _}
`{@PartialOrder B _ _}
  : PartialOrder (pair_instance_le).
Proof.
  split; eauto with typeclass_instances.
  - split; eauto with typeclass_instances.
  - intros ? ? H1e ? ? H2e; unfold le, pair_instance_le.
    rewrite H1e, H2e. tauto.
  - intros ? ?. unfold le, pair_instance_le. intros ? ?.
    repnd. split; simpl; eapply  po_antisym; eauto.
Qed.

Instance OrderPreservingLePlusPair
`{@PairLike Pair A B mkpair pfst psnd}
`{Ring A}  `{Ring B}
`{Le A}
`{Le B}
`{@PartialOrder A _ _}
`{@PartialOrder B _ _}
  {_:forall a:A, OrderPreserving (plus a)}
  {_:forall b:B, OrderPreserving (plus b)}
(z : Pair): 
  OrderPreserving (plus z).
Proof.
  split; eauto  with typeclass_instances.
  - split; eauto with typeclass_instances;
    split; eauto with typeclass_instances;
    split; eauto with typeclass_instances;
    unfold plus,PlusPairLike;
    repeat rewrite pairLikeFst;
    repeat rewrite pairLikeSnd;
    rewrite H8;  auto.
  - intros ? ?. unfold le, pair_instance_le.
    intros. repnd;
    simpl.
    split;
    unfold plus,PlusPairLike;
    repeat rewrite pairLikeFst;
    repeat rewrite pairLikeSnd;
    eauto with typeclass_instances.
Qed.

Instance MultLeSemiRingOrderPair
`{@PairLike Pair A B mkpair pfst psnd}
`{Ring A}  `{Ring B}
`{Le A}
`{Le B}
  {Ha:∀ (x y :  A) , PropHolds (0 ≤ x) → PropHolds (0 ≤ y) 
      → PropHolds (0 ≤ x * y) }
  {Hb:∀ (x y :  B) , PropHolds (0 ≤ x) → PropHolds (0 ≤ y) 
      → PropHolds (0 ≤ x * y) }:
  ∀ x y : (Pair) , PropHolds (0 ≤ x) → PropHolds (0 ≤ y) → PropHolds (0 ≤ x * y) .
Proof.
    unfold le, pair_instance_le, PropHolds.
    unfold  PropHolds in Ha, Hb.
    simpl.
    intros.
    unfold zero, ZeroPairLike in *.
    rewrite pairLikeFst in H4, H5;
    rewrite pairLikeSnd in H4, H5;
    repnd; 
    simpl;
    split;
    unfold mult,MultPairLike;
    repeat rewrite pairLikeFst in *;
    repeat rewrite pairLikeSnd in *;
    eauto with typeclass_instances.
Qed.



Require Import MathClasses.orders.rings.

Local Existing Instance RingPairLike.

Instance 
PairSemiringOrder 
`{@PairLike Pair A B mkpair pfst psnd}
`{Ring A}  `{Ring B}
`{Le A}
`{Le B}
    `{@orders.SemiRingOrder A equiv plus mult zero one le}
    `{@orders.SemiRingOrder B equiv plus mult zero one le}:
    `{orders.SemiRingOrder (@canonical_names.le Pair _)}.
Proof.
  apply from_ring_order;
  eauto with typeclass_instances;[].
  apply OrderPreservingLePlusPair.
Qed.

Require Import CoRN.logic.Stability.


Instance StableLePair
`{@PairLike Pair A B mkpair pfst psnd}
`{Le A}
`{Le B} :
  (forall x y : A, Stable (x≤y))
  -> (forall x y : B, Stable (x≤y))
  -> (forall a b : Pair, Stable (a≤b)).
Proof.
  intros Hca Hcb  a b.
  apply stable_conjunction; eauto.
Qed.


End ForgetTypeclassInstances.




(*
Lemma foldPlusLine `{Ring A} : forall xa xb ya yb: Cart2D A,
  {| minxy := xa + xb; maxxy :=ya + yb |} = {|minxy :=xa; maxxy :=ya|} 
    + {|minxy:=xb; maxxy:=yb|}.
Proof.
    intros. reflexivity.
Qed.
*)
