Require Import MathClasses.interfaces.canonical_names.
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