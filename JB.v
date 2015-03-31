
Require Export icreate.

Open Scope mc_scope.

(* in general, the type of [te] should be [Time] *)
Lemma DI0 : ∀ (F F' : Cart2D TContR) (LD : TContR) (te : QTime),
  isDerivativeOf (X F') (X F)
  -> isDerivativeOf (Y F') (Y F)
  -> isDerivativeOf LD ((X F)* (X F) + (Y F)* (Y F) - 1)
  -> (getF ((X F)* (X F) + (Y F)* (Y F) - 1)) 0 = 0
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
  -> (∀ (t : QTime), (0 <= t <= te) ->  {LD} t = 0)
  -> {Inv} te = 0.
Proof.
  intros ? ? ? Hld Heq0 Ht.
  rewrite <- Heq0.
  eapply TDerivativeEqQ0; eauto.
  simpl. eauto 1 with ROSCOQ.
Qed.

  
Lemma DI' : ∀ (F F' : Cart2D TContR) (LD : TContR) (te : QTime),
  isDerivativeOf (X F') (X F)
  -> isDerivativeOf (Y F') (Y F)
  -> isDerivativeOf LD ((X F) * (X F) + (Y F) * (Y F) - 1)
  -> ∀ (t : QTime), 
        {X F'} t = - {Y F} t 
        -> {Y F'} t =  {X F} t
        -> {LD} t = 0.
Proof.
  intros? ? ? ?  H1d H2d H3d ? H1eq H2eq.
  eapply DerivativeNormSqr with (Y':=(Y F')) in H1d; eauto.
  clear H2d.
  pose proof (TContRDerivativeConst (closel [0]) I (-1)) as Hconst.
  pose proof (TContRDerivativePlus  H1d Hconst) as Hadd.
  clear H1d Hconst.
  eapply isIDerivativeOfWdl in Hadd;
    [|apply cm_rht_unit_unfolded].
  unfold canonical_names.negate, Negate_instance_IR in Hadd.
  eapply isIDerivativeOfWdr in Hadd;
    [ | rewrite <- FConstOppIn; reflexivity].
  eapply isDerivativeUnique in Hadd; [| exact H3d].
  clear H3d.
  unfold canonical_names.equiv.
  rewrite Hadd.
  autorewrite with IContRApDown.
  rewrite H1eq.
  rewrite H2eq.
  autounfold with IRMC.
  ring.
Qed.


Lemma DIEx : ∀ (F F' : Cart2D TContR) (LD : TContR) (te : QTime),
  isDerivativeOf (X F') (X F)
  -> isDerivativeOf (Y F') (Y F)
  -> isDerivativeOf LD ((X F)* (X F) + (Y F)* (Y F) - 1)
  -> (getF ((X F)* (X F) + (Y F)* (Y F) - 1)) 0 = 0
  -> (∀ (t : QTime), (0 <= t <= te ) 
      -> {X F'} t = - {Y F} t 
          ∧ {Y F'} t =  {X F} t)
  -> (getF ((X F)* (X F) + (Y F)* (Y F) - 1)) te = 0.
Proof.
  intros ? ? ? ? H1d H2d Hld Heq0 Ht.
  eapply DI; eauto.
  intros ? Hb.
  apply Ht in Hb. clear Ht.
  destruct Hb as [Htl Htr].
  eapply DI'; eauto.
Qed.
