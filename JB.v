
Require Export icreate.

Open Scope mc_scope.

(* in general, the type of [te] should be [Time] *)
Lemma DI0 : ∀ (F F' : Cart2D TContR) (LD : TContR) (te : QTime),
  isDerivativeOf (X F') (X F)
  -> isDerivativeOf (Y F') (Y F)
  -> isDerivativeOf LD ((X F)* (X F) + (Y F)* (Y F) - 1)
  -> (getF ((X F)* (X F) + (Y F)* (Y F) - 1)) (mkQTime 0 I) = 0
  -> (∀ (t : QTime), ((mkQTime 0 I) <= t <= te ) 
      -> {X F'} t = - {Y F} t 
          ∧ {Y F'} t =  {X F} t 
          ∧ {LD} t = 0
          )
  -> (getF ((X F)* (X F) + (Y F)* (Y F) - 1)) te = 0.
Proof.
  intros ? ? ? ? H1d H2d Hld Heq0 Ht.
  rewrite <- Heq0.
  eapply TDerivativeEqQ0; eauto.
  - simpl. eauto 1 with ROSCOQ.
  - apply Ht.
Qed.

Lemma DI : ∀ (Inv LD : TContR) (te : QTime),
  isDerivativeOf LD Inv
  -> {Inv} (mkQTime 0 I) = 0
  -> (∀ (t : QTime), ((mkQTime 0 I) <= t <= te) ->  {LD} t = 0)
  -> {Inv} te = 0.
Proof.
  intros ? ? ? Hld Heq0 Ht.
  rewrite <- Heq0.
  eapply TDerivativeEqQ0; eauto.
  simpl. eauto 1 with ROSCOQ.
Qed.

Add Ring IRisaRing: (CRing_Ring TContR).

Lemma isDerivativeUnique:
  ∀ (F F1' F2' : TContR),
  isDerivativeOf F1' F
  → isDerivativeOf F2' F
  → F1' [=]  F2'.
Admitted.

  
Lemma DI' : ∀ (F F' : Cart2D TContR) (LD : TContR) (te : QTime),
  isDerivativeOf (X F') (X F)
  -> isDerivativeOf (Y F') (Y F)
  -> isDerivativeOf LD ((X F) [*] (X F) [+] (Y F) [*] (Y F)  [+] - 1)
  -> ∀ (t : QTime), 
        ((mkQTime 0 I) <= t <= te) 
        -> {X F'} t = - {Y F} t 
        -> {Y F'} t =  {X F} t
        -> {LD} t = 0.
Proof.
  intros? ? ? ?  H1d H2d H3d ? Htb H1eq H2eq.
  eapply DerivativeNormSqr with (Y':=(Y F')) in H1d; eauto.
  eapply TContRDerivativePlus with (F:= (X F[*]X F[+]Y F[*]Y F)) 
        (G:=-1) (G':=0) in H1d; eauto.
  eapply isDerivativeUnique in H1d.
  simpl un H1d H
  Focus 2. exact H3d.

