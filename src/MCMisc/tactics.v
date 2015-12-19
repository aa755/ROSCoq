Require Import MathClasses.interfaces.canonical_names.

Lemma eqEquiv `{e:Equiv A} `{Equivalence A e}: ∀ a b:A,
eq a b
-> a=b.
Proof using .
intros ? ? Hs. rewrite Hs. reflexivity.
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