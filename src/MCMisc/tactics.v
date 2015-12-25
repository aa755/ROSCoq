Require Import MathClasses.interfaces.canonical_names.

Lemma eqEquiv `{e:Equiv A} `{Equivalence A e}: ∀ a b:A,
eq a b
-> a=b.
Proof using .
intros ? ? Hs. rewrite Hs. reflexivity.
Qed.

(*not really a tactic*)
Lemma inBetweenExpand `{PreOrder A r} : forall a b c a' c':A,
(r a b /\ r b c) 
-> (r a' a /\ r c c')
-> (r a' b /\ r b c').
Proof using.
  intros ? ? ? ? ? H1 H2. destruct H1, H2.
  split; eapply transitivity; eauto.
Qed.

Require Import MathClasses.interfaces.orders.

Lemma po_properL:
  ∀ (A : Type) (Ae : Equiv A) (Ale : Le A) (a:A),
  PartialOrder Ale → Equivalence (@equiv A _) → Proper (equiv ==> iff)
    (fun x=> le x a).
Proof using.
  intros ? ? ? ? ? ? ? ? ?. apply po_proper; auto.
Qed.

Ltac mcremember x y H:=
remember x as y eqn:H;
apply eqEquiv in H.

Ltac fequivHyp H f :=
    let He := fresh H "e" in
    match type of H with
    equiv ?x ?y => assert (equiv (f x) (f y)) as He
    by (rewrite H;reflexivity)
    end.
    
Ltac fequiv :=
    let Heq := fresh "Heq" in
    match goal with
    [ |- equiv (?f ?x) (?f ?y)]=> assert (equiv x y) as Heq;
      [| try (setoid_rewrite Heq; reflexivity)]
    end.