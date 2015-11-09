Require Export CoRN.ftc.FTC.

Require Export CanonicalNotations.
Instance NormSpace_instance_IR : NormSpace IR IR := AbsIR.

Definition Q2R  (q: Q) : IR := (inj_Q IR q).
Coercion  Q2R : Q >-> st_car.

Require Export CoRN.ftc.Derivative.   
Require Export CoRN.ftc.Integral.
Lemma inDomDerLeft : 
forall {F F': PartFunct IR} {a b : IR} {Hab : a[<]b},
Derivative_I Hab F F'
-> (Dom F a).
Proof.
  intros ? ? ? ? ?  der.
  apply derivative_imp_inc in der.
  apply der. unfold compact. split.
  - apply leEq_reflexive.
  - apply less_leEq. trivial.
Defined.


Lemma reciprocalNeg : forall (C: CField) (x: C) (xp : x [#] [0]) (nxp : ([--]x) [#] [0]),
   f_rcpcl ([--]x) nxp [=] [--] (f_rcpcl x xp).
Proof.
  intros ? ? ? ?.
  apply mult_cancel_lft with (z:=[--]x);[exact nxp|].
  rewrite field_mult_inv.
  rewrite inv_mult_invol.
  rewrite field_mult_inv.
  reflexivity.
Qed.


Lemma inDomDerRight : 
forall {F F': PartFunct IR} {a b : IR} {Hab : a[<]b},
Derivative_I Hab F F'
-> (Dom F b).
Proof.
  intros ? ? ? ? ?  der.
  apply derivative_imp_inc in der.
  apply der. unfold compact. split.
  - apply less_leEq. trivial.
  - apply leEq_reflexive.
Defined.

Hint Rewrite cg_inv_zero : CoRN.

Lemma cll : forall {a b}, a[<]b 
  -> (clcr a b) a.
intros ? ? Hlt. simpl.
split.
  - apply leEq_reflexive.
  - apply less_leEq. trivial.
Defined.

Lemma clr : forall {a b}, a[<]b 
  -> (clcr a b) b.
intros ? ? Hlt. simpl.
split.
  - apply less_leEq. trivial.
  - apply leEq_reflexive.
Defined.

Lemma clclLend : forall {a b} (cI : compact_ (clcr a b)),
 Lend  cI = a.
Proof.
 simpl. reflexivity.
Defined.

Lemma clclRend : forall {a b} (cI : compact_ (clcr a b)),
 Rend  cI = b.
Proof.
 simpl. reflexivity.
Defined.

Definition equivInterval (ia ib : interval) :=
 forall x,  (ia x) IFF (ib x).

Lemma derivContI' :
forall {F F' : PartIR} {a b : IR}
  {Hab : a [<] b}
  (derivF : Derivative (clcr a b) Hab F F'),
  Continuous_I (less_leEq _ _ _ Hab) F'.
Proof.
  intros.
  apply Derivative_imp_Continuous' in derivF.
  assert (compact_ (clcr a b)) as Ci
     by (apply less_leEq; trivial).
  apply Int_Continuous with (cI := Ci) (H:=less_leEq IR a b Hab) in derivF .
  trivial.
Defined.

Lemma minmaxincluded: 
forall a b (Hab : a [<] b),
 included 
     (Compact (Min_leEq_Max a b)) 
     (Compact (less_leEq IR a b Hab)).
Proof.
 intros. unfold compact. simpl.
 intros x Hc. destruct Hc as [Hcl Hcr].
 apply less_leEq in Hab.
 rewrite leEq_imp_Min_is_lft in Hcl;[| trivial].
 rewrite leEq_imp_Max_is_rht in Hcr;[| trivial].
 split; trivial.
Qed.

(** if we know that [a<b] many hypothesis in Barrow
    can be removed *)
Lemma Barrow2  : forall (F F' : PartIR) {a b : IR}
  (Hab : a [<] b) (derivF : Derivative (clcr a b) Hab F F'),
  let Hc := derivContI' derivF in
  let Hb := Derivative_imp_inc _ _ _ _ derivF b (clr Hab) in
  let Ha := Derivative_imp_inc _ _ _ _ derivF a (cll Hab) in 
  integral a b (less_leEq _ _ _ Hab) F' Hc  [=]F b Hb[-]F a Ha.
Proof.
  intros.
  assert (Continuous_I (Min_leEq_Max a b) F') as HF.
  - eapply included_imp_contin; eauto.
    apply minmaxincluded.
  - rewrite <- Integral_integral with (HF := HF).
    apply Barrow.
    eapply Derivative_imp_Continuous';
    eauto.
Qed.

Definition UBoundInCompInt {a b} (Hab : a [<]b)
 (F : PartIR) (ub : IR) 
   :=
forall x : IR,
  Compact (less_leEq IR a b Hab) x 
  -> forall Hx : Dom F x, F x Hx[<=]ub.


(** Combines Barrow's theorem ([Barrow2]) and 
    [ub_integral]*)
Lemma AntiderivativeUB : 
forall (F F': PartFunct IR) (a b : IR) (Hab : a[<]b)
     (derivF : Derivative (clcr a b) Hab F F') (c : IR),
     let Hdb := Derivative_imp_inc _ _ _ _ derivF b (clr Hab) in
     let Hda := Derivative_imp_inc _ _ _ _ derivF a (cll Hab) in
     UBoundInCompInt Hab F' c
     -> (F b Hdb[-] F a Hda)[<=]c[*](b[-]a).
Proof.
  intros ? ? ? ? ? ? ? ? ?  Hlub.
  subst Hda. subst Hdb.
  rewrite <- Barrow2.
  apply ub_integral.
 exact Hlub.
Qed.

(** See [core.TDerivativeUBQ]
    for a stronger version for rationals,
    Basically, Hab will have type [a <= b] *)
Lemma AntiderivativeUB2 : 
forall (F F': PartFunct IR) (a b : IR) (Hab : a[<]b)
     (derivF : Derivative (clcr a b) Hab F F') (c : IR)
     Hdb Hda,
     UBoundInCompInt Hab F' c
     -> (F b Hdb[-] F a Hda)[<=]c[*](b[-]a).
Proof.
  intros ? ? ? ? ? ? ? ? ?  Hlub.
  pose proof (pfwdef _ F b b Hdb
               (Derivative_imp_inc _ _ _ _ derivF b (clr Hab))
                (eq_reflexive _ _) ) 
             as Hrwb.
  rewrite Hrwb. clear Hrwb.
  pose proof (pfwdef _ F a a Hda
               (Derivative_imp_inc _ _ _ _ derivF a (cll Hab))
                (eq_reflexive _ _) ) 
             as Hrwa.
  rewrite Hrwa. clear Hrwa.
 apply AntiderivativeUB; auto.
Qed.

(** it is not possible to change [<] to [<=] in [Hab] because
    unlike continuity, definitions of 
    derivative ([Derivative] and [Derivative_I])
    require a proper interval *)
    
Definition LBoundInCompInt {a b} (Hab : a [<]b)
 (F : PartIR) (lb : IR) 
   :=
forall x : IR,
  Compact (less_leEq IR a b Hab) x 
  -> forall Hx : Dom F x, lb [<=] F x Hx.


(** Combines Barrow's theorem ([Barrow2]) and 
    [lb_integral]*)
Lemma AntiderivativeLB : 
forall (F F': PartFunct IR) (a b : IR) (Hab : a[<]b)
     (derivF : Derivative (clcr a b) Hab F F') (c : IR),
     let Hdb := Derivative_imp_inc _ _ _ _ derivF b (clr Hab) in
     let Hda := Derivative_imp_inc _ _ _ _ derivF a (cll Hab) in
     LBoundInCompInt Hab F' c
     -> c[*](b[-]a) [<=] (F b Hdb[-] F a Hda).
Proof.
  intros ? ? ? ? ? ? ? ? ?  Hlub.
  subst Hda. subst Hdb.
  rewrite <- Barrow2.
  apply lb_integral.
 exact Hlub.
Qed.

(** See [core.TDerivativeUBQ]
    for a stronger version for rationals,
    Basically, Hab will have type [a <= b] *)
Lemma AntiderivativeLB2 : 
forall (F F': PartFunct IR) (a b : IR) (Hab : a[<]b)
     (derivF : Derivative (clcr a b) Hab F F') (c : IR)
     Hdb Hda,
     LBoundInCompInt Hab F' c
     -> c[*](b[-]a) [<=] (F b Hdb[-] F a Hda).
Proof.
  intros ? ? ? ? ? ? ? ? ?  Hlub.
  pose proof (pfwdef _ F b b Hdb
               (Derivative_imp_inc _ _ _ _ derivF b (clr Hab))
                (eq_reflexive _ _) ) 
             as Hrwb.
  rewrite Hrwb. clear Hrwb.
  pose proof (pfwdef _ F a a Hda
               (Derivative_imp_inc _ _ _ _ derivF a (cll Hab))
                (eq_reflexive _ _) ) 
             as Hrwa.
  rewrite Hrwa. clear Hrwa.
 apply AntiderivativeLB; auto.
Qed.


Require Import Coq.QArith.Qfield.
Require Import Coq.QArith.Qring.
Require Import Psatz.

Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Add Ring IRisaRing: (CRing_Ring IR).
Require Import Psatz.
Require Import Setoid.

Lemma shift_zeroR_leEq_minus :
  forall ft fq : IR, ft[<=]fq -> ft[-]fq[<=][0].
Proof.
  intros ? ? Hle.
  apply shift_minus_leEq.
  ring_simplify.
  trivial.
Qed.

Lemma minusInvR : forall a b:IR, [--](a[-]b)[=](b[-]a).
Proof.
  intros. unfold cg_minus.
  ring.
Qed.

Lemma minusSwapLe : forall (x y z : IR),
  x [-] y [<=] z -> x [-] z [<=] y.
Proof.
  intros  ? ? ? Hncl.
  apply shift_leEq_plus in Hncl.
  rewrite cag_commutes in Hncl.
  apply shift_minus_leEq in Hncl.
  trivial.
Qed.

Lemma seq_refl: forall x y : IR, x = y -> x[=] y.
  intros ? ? Heq.
  rewrite Heq.
  apply eq_reflexive.
Qed.

Require Import Coq.Unicode.Utf8.


Lemma QeqQle : ∀ x y,
  Qeq x y -> Qle x y.
Proof.
  intros ? ?  Hq.
  rewrite Hq.
  apply Qle_refl.
Qed.

Lemma TwoForRing : (2 # 1 = 1+1)%Q.
  reflexivity.
Qed.

Lemma QmultOverQminusR : ∀ a b c : Q,
  ((a - b) * c == a * c - b * c)%Q.
Proof.
  intros ? ? ?.
  ring.
Qed.


Lemma foldQminus : ∀ a b : Q,
  (a + - b == (a - b) )%Q.
Proof.
  intros ? ?. reflexivity.
Qed.


Lemma crmult_Qmult : forall (a b : Q),
  (a*b)%Q = a[*]b.
  reflexivity.
Qed.

Lemma IRDistMinus : ∀ (a b c : IR),
  (a [-] b)[*] c [=] a[*] c [-] b[*] c.
Proof.
  intros. unfold cg_minus. ring.
Qed.

Hint Rewrite cg_zero_inv cg_inv_inv : CoRN.
Hint Resolve AbsIR_nonneg: CoRN.

(** Move to core *)

Lemma injQ_nonneg: ∀ q,
   (0<=q)%Q -> ([0] [<=] Q2R q).
Proof.
  intros ? H.
  rewrite <- inj_Q_Zero.
  apply inj_Q_leEq.
  assumption.
Qed.

Hint Resolve injQ_nonneg : CoRN.

Lemma pfstrlt:  forall (p : PartFunct IR) (x y : IR) 
      (Hx : Dom p x)
      (Hy : Dom p y), 
        p x Hx[<]p y Hy 
        -> x[<=]y
        -> x[<]y.
Proof.
  intros ? ? ? ? ? Hpp Hle.
  apply less_imp_ap in Hpp.
  apply pfstrx in Hpp.
  apply ap_imp_less in Hpp.
  apply leEq_def in Hle. unfold Not in Hle.
  destruct Hpp; tauto.
Qed.


Lemma pfstrgt:  forall (p : PartFunct IR) (x y : IR) 
      (Hx : Dom p x)
      (Hy : Dom p y), 
        p x Hx[<]p y Hy 
        -> y[<=]x
       -> y[<]x.
Proof.
  intros ? ? ? ? ? Hpp Hle.
  apply less_imp_ap in Hpp.
  apply pfstrx in Hpp.
  apply ap_imp_less in Hpp.
  apply leEq_def in Hle. unfold Not in Hle.
  destruct Hpp; tauto.
Qed.

Lemma minusInvQ : forall a b:Q, [--](a[-]b)[=](b[-]a).
Proof.
  intros. unfold cg_minus.
  simpl. ring.
Qed.


Lemma minusQ2R0:  ∀ x:IR, x[-]0%Q [=] x.
Proof.
  intros.
  unfold Q2R.
  rewrite  inj_Q_Zero, cg_inv_zero.
  reflexivity.
Qed.

Lemma plusQ2R0:  ∀ x:IR, x[+]0%Q [=] x.
Proof.
  intros.
  unfold Q2R.
  rewrite  inj_Q_Zero. ring.
Qed.

Lemma multQ2R0R:  ∀ x:IR, x[*]0%Q [=] 0%Q.
Proof.
  intros.
  unfold Q2R.
  rewrite  inj_Q_Zero. ring.
Qed.

Lemma multQ2R0L:  ∀ x:IR, (Q2R 0)[*]x [=] 0%Q.
Proof.
  intros.
  unfold Q2R.
  rewrite  inj_Q_Zero. ring.
Qed.

Hint Rewrite minusQ2R0 plusQ2R0 multQ2R0R multQ2R0L : CoRN.

Lemma AbsMinusUB : ∀ (a t eps : IR),
  AbsIR (t[-]a)[<=] eps
  -> t [<=] a [+] eps.
Proof.
  intros ? ? ? Habs.
  rewrite AbsIR_minus in Habs.
  apply AbsIR_bnd. assumption.
Qed.

Lemma AbsMinusLB : ∀ (a t eps : IR),
  AbsIR (t[-]a)[<=] eps
  -> a [-] eps [<=] t.
Proof.
  intros ? ? ? Habs.
  apply AbsIR_bnd in Habs.
  apply shift_minus_leEq.
  assumption.
Qed.

Lemma eqImpliesLeEq : ∀ a b : IR,
  a [=] b -> a [<=] b.
Proof.
  intros ? ? H. rewrite H.
  apply leEq_reflexive.
Qed.


Instance Proper_Qeq_Inj_Q :
  Proper (Qeq ==> @st_eq IR) (inj_Q IR).
Proof.
  intros a b Hab.
  apply inj_Q_wd.
  auto.
Qed.
  

Lemma Q2R0IsR0 : Q2R 0 [=] [0].
  unfold Q2R.
  apply inj_Q_Zero.
Qed.

Lemma AbsIRLe0 : ∀ x,
  AbsIR x [<=] [0]
  -> x [=] [0].
Proof.
  intros ? Hc. apply AbsIR_imp_AbsSmall in Hc.
  unfold AbsSmall in Hc. destruct Hc as [Hcl Hcr].
  rewrite cg_zero_inv in Hcl.
  apply leEq_imp_eq; assumption.
Qed.
Hint Rewrite cg_minus_correct AbsIRz_isz cring_mult_zero : CoRN.


Hint Resolve less_leEq_trans leEq_less_trans plus_resp_less_leEq
  plus_resp_leEq_less minus_resp_less_leEq plus_resp_pos_nonneg
  leEq_inj_Q leEq_wdr leEq_wdr leEq_reflexive eq_imp_leEq
  leEq_imp_eq leEq_imp_eq leEq_transitive (leEq_inj_Q IR) less_leEq
  Min_leEq_rht Min_leEq_lft
  shift_zero_leEq_minus shift_minus_leEq shift_zeroR_leEq_minus
  pos_two pos_one rht_leEq_Max 
  lft_leEq_Max Min_leEq_Max: CoRN.

Hint Immediate eq_reflexive_unfolded : CoRN.

Lemma addNNegLeEq : ∀ ( a eps : IR),
  [0] [<=] eps 
  -> a [<=] a [+] eps.
Proof.
  intros ? ? Hle.
  assert (a[+][0][<=]a[+]eps) as H.
  apply plus_resp_leEq_both; eauto 2 with CoRN.
  ring_simplify in H.
  assumption.
Qed.

Lemma MinusNNegLeEq : ∀ ( a eps : IR),
  [0] [<=] eps 
  -> a [-] eps [<=] a.
Proof.
  intros ? ? Hle.
  assert (a [-] eps[<=]a[-][0]) as H.
  apply minus_resp_leEq_both; eauto 2 with CoRN.
  unfold cg_minus in H. ring_simplify in H.
  assumption.
Qed.

Hint Resolve addNNegLeEq MinusNNegLeEq Min_leEq_rht: CoRN.

Lemma leAddRhs :
forall (a b : IR), 
    [0][<=]b -> a[<=]a[+]b.
Abort.

Lemma ltAddRhs :
forall (a b : IR), 
    [0][<]b -> a[<]a[+]b.
  intros ? ? Hlt.
  pose proof (leEq_reflexive _ a) as Hr.
  apply (plus_resp_less_leEq _ _ _ _ _ Hlt) in Hr.
  eapply less_wdl in Hr;[|apply cm_lft_unit_unfolded].
  eapply less_wdr;[| apply cag_commutes_unfolded].
  trivial.
Qed.

Lemma closeRationalR : forall (a b t d : IR) (Hab : a [<=] b),
  Compact Hab t
  -> t[<]b
  -> [0][<]d
  -> {q : Q | Compact Hab q /\
                      AbsIR (t[-]q)[<=]d}.
Proof.
  intros ? ? ? ? ? p Hcc Hdp.
  pose proof (less_Min _ _ _ (ltAddRhs t d Hdp) Hcc) as Hmlt.
  pose proof (Q_dense_in_CReals' _ _ _ Hmlt) as Hqr.
  destruct Hqr as [q Hqr Hql].
  exists q.
  simpl in p. unfold Q2R in p. destruct p as [pl pr].
  assert ( a[<=]inj_Q IR q) as Haq by (eauto using
        less_leEq, leEq_less_trans).
  assert (inj_Q IR q[<=] b) as Hqb by (eauto using
      less_leEq,
      less_leEq_trans,
      Min_leEq_rht).
  split;[exact (Haq,Hqb)|].
  rewrite AbsIR_minus. unfold Q2R.
  rewrite AbsIR_eq_x;[|eauto 4 using 
        shift_zero_leEq_minus, less_leEq].
  apply shift_minus_leEq.
  rewrite cag_commutes_unfolded.
  eauto using
        less_leEq,leEq_less_trans,leEq_reflexive,
        less_leEq_trans,Min_leEq_lft.
Defined.

Lemma ltMinusRhs: 
  forall (x y: IR), 
    [0] [<]y -> x[-]y[<]x.
Proof.
  intros.
  apply shift_minus_less.
  apply ltAddRhs; auto.
Qed.



Lemma closeRationalL : forall (a b t d : IR) (Hab : a [<=] b),
  Compact Hab t
  -> a[<]t
  -> [0][<]d
  -> {q : Q | Compact Hab q /\
                      AbsIR (t[-]q)[<=]d}.
Proof.
  intros ? ? ? ? ? p Hcc Hdp.
  pose proof (Max_less _ _ _ (ltMinusRhs _ d Hdp) Hcc) as Hmlt.
  pose proof (Q_dense_in_CReals' _ _ _ Hmlt) as Hqr.
  destruct Hqr as [q Hqr Hql].
  exists q.
  simpl in p. unfold Q2R in p. destruct p as [pl pr].
  assert (inj_Q IR q[<=] b) as Hqb by (eauto using
        less_leEq, less_leEq_trans).
  assert (a[<=] inj_Q IR q) as Haq by (eauto using
      less_leEq,
      less_leEq_trans,
      leEq_less_trans,
      rht_leEq_Max).
  split;[exact (Haq,Hqb)|].
  rewrite AbsIR_eq_x;[|eauto 4 using 
        shift_zero_leEq_minus, less_leEq].
  apply shift_minus_leEq.
  apply shift_leEq_plus'.
  unfold Q2R.
  pose proof (lft_leEq_Max (t[-]d) a).
  apply less_leEq.
  eapply leEq_less_trans; eauto.
Qed.

Lemma ContFunQRLeAux : forall (f : PartIR)  (a b : Q) (c : IR)
(cc : Continuous (clcr a b) f),
(forall (t:Q) (p: (clcr a b) t), (f t ((fst cc) _ p) [<=] c))
-> (forall (t:IR) (p: (clcr a b) t), (f t ((fst cc) _ p) [<=] c)).
Proof.
  intros ? ? ? ? ? Hq ? ?.
  apply leEq_def.
  intros Hc.
  unfold Continuous in cc.
  pose proof (Qlt_le_dec b a) as Hd.
  destruct Hd as [Hd | Hd].
- simpl in p. destruct p as [pl pr].
  assert ((Q2R a) [<=] (Q2R b)) as Hqq by 
  eauto using leEq_transitive.
  apply leEq_inj_Q in Hqq.
  simpl in Hqq. lra.
- destruct cc as [HI  HC].
  simpl in Hq. pose proof Hd as Hdb.
  apply (inj_Q_leEq IR) in Hd.
  simpl in Hc.
  specialize (HC _ _ Hd).
  unfold compact in HC. simpl in HC.
  lapply HC;[clear HC; intro HC
            |intros x Hx; simpl; tauto].
  unfold  Continuous_I in HC.
  apply snd in HC. pose proof Hc as Hcb.
  apply shift_zero_less_minus in Hc.
  remember ((f t (HI t p)) [-] c) as eps.
  apply pos_div_two in Hc.
  specialize (HC _ Hc).
  destruct HC as [d Hdp HC].
  (** need to come up with a rational (say [q]) [d]-close 
    to [t] and also in [(clcr a b)].
    Then we can use [Hq q] and [HC t q)] to get a contradiction
    [q] can be on either side of [t].
    Lets focus on RHS.
    so, [q] must lie in (olor t (Min (t[+]d) b))
    Since rationals are dense in reals, it suffices
    to prove that t < (Min (t[+]d) b)
 *)
  pose proof (leEq_less_or_equal _ _ _ (snd p)) as Heq.
  apply Heq. intros Hcc. simpl in Hq. clear Heq.
  pose proof (Hq b (Hd,leEq_reflexive _ _)) as Hqb.
  destruct Hcc as [Hcc| Hcc];
  [ | pose proof (pfwdef _ _ _ _ (HI t p) 
                (HI b (Hd, leEq_reflexive IR b)) Hcc) as Hr;
      rewrite <- Hr in Hqb;
      apply leEq_def in Hqb;
      unfold Not in Hqb; tauto].
  clear Hqb.

pose proof (closeRationalR _ _ _ _ 
    Hd p Hcc Hdp) as Hqq.
destruct Hqq as [q Hqq].
destruct Hqq as [Hcomp Hab].
  specialize (HC t q p Hcomp (HI t p) (HI (inj_Q IR q) Hcomp) Hab).
  clear Hcc Hdp.
  subst eps. clear Hc.
  remember (f t (HI t p)) as ft.
  clear Heqft. unfold Q2R in Hq.
  apply shift_mult_leEq' in HC; [|apply pos_two].
  specialize (Hq q Hcomp).
  unfold Q2R in HC.
  remember (f (inj_Q IR q) (HI (inj_Q IR q) Hcomp)) as fq.
  clear Heqfq.
  assert (fq[<]ft) as Hlqt by eauto using leEq_less_trans.
  (** Now we need to prove ft[<=]fq *)
  rewrite AbsIR_eq_x in HC;[|eauto using 
      shift_zero_leEq_minus,
      less_leEq].
  apply (plus_resp_leEq_both _ _ _ _ _ HC) in Hq.
  rewrite <- cg_cancel_mixed in Hq.
  rewrite <- x_plus_x in Hq.
  apply shift_leEq_minus in Hq.
  remember (ft[-]fq) as ftmx.
  apply shift_leEq_minus in Hq.
  rewrite cg_minus_correct in Hq.
  subst ftmx.
  apply shift_leEq_plus in Hq.
  ring_simplify in Hq.
  apply leEq_def in Hq.
  unfold Not in Hq. tauto.
Qed.

(** It might be possible to do this proof 
    using AbsIR_approach_zero *)
Lemma ContFunQRGeAux : forall (f : PartIR)  (a b : Q) (c : IR)
(cc : Continuous (clcr a b) f),
(forall (t:Q) (p: (clcr a b) t), (c [<=] f t ((fst cc) _ p)))
-> (forall (t:IR) (p: (clcr a b) t), (c [<=] f t ((fst cc) _ p))).
Proof.
  intros ? ? ? ? ? Hq ? ?.
  apply leEq_def.
  intros Hc.
  unfold Continuous in cc.
  pose proof (Qlt_le_dec b a) as Hd.
  destruct Hd as [Hd | Hd].
- simpl in p. destruct p as [pl pr].
  assert ((Q2R a) [<=] (Q2R b)) as Hqq by 
  eauto using leEq_transitive.
  apply leEq_inj_Q in Hqq.
  simpl in Hqq. lra.
- destruct cc as [HI  HC].
  simpl in Hq. pose proof Hd as Hdb.
  apply (inj_Q_leEq IR) in Hd.
  simpl in Hc.
  specialize (HC _ _ Hd).
  unfold compact in HC. simpl in HC.
  lapply HC;[clear HC; intro HC
            |intros x Hx; simpl; tauto].
  unfold  Continuous_I in HC.
  apply snd in HC. pose proof Hc as Hcb.
  apply shift_zero_less_minus in Hc.
  remember ((f t (HI t p)) [-] c) as eps.
  apply pos_div_two in Hc.
  specialize (HC _ Hc).
  destruct HC as [d Hdp HC].
  (** need to come up with a rational (say [q]) [d]-close 
    to [t] and also in [(clcr a b)].
    Then we can use [Hq q] and [HC t q)] to get a contradiction
    [q] can be on either side of [t].
    Lets focus on RHS.
    so, [q] must lie in (olor t (Min (t[+]d) b))
    Since rationals are dense in reals, it suffices
    to prove that t < (Min (t[+]d) b)
 *)
  pose proof (leEq_less_or_equal _ _ _ (snd p)) as Heq.
  apply Heq. intros Hcc. simpl in Hq. clear Heq.
  pose proof (Hq b (Hd,leEq_reflexive _ _)) as Hqb.
  destruct Hcc as [Hcc| Hcc];
  [ | pose proof (pfwdef _ _ _ _ (HI t p) 
                (HI b (Hd, leEq_reflexive IR b)) Hcc) as Hr;
      rewrite <- Hr in Hqb;
      apply leEq_def in Hqb;
      unfold Not in Hqb; tauto].
  clear Hqb.
pose proof (closeRationalR _ _ _ _ 
    Hd p Hcc Hdp) as Hqq.
destruct Hqq as [q Hqq].
destruct Hqq as [Hcomp Hab].
  specialize (HC t q p Hcomp (HI t p) (HI (inj_Q IR q) Hcomp) Hab).
  clear Hcc Hdp.
  subst eps. clear Hc.
  remember (f t (HI t p)) as ft.
  clear Heqft. unfold Q2R in Hq.
  apply shift_mult_leEq' in HC; [|apply pos_two].
  specialize (Hq q Hcomp).
  unfold Q2R in HC.
  remember (f (inj_Q IR q) (HI (inj_Q IR q) Hcomp)) as fq.
  clear Heqfq.
  assert (ft[<]fq) as Hlqt by eauto using less_leEq_trans.
  (** Now we need to prove ft[<=]fq *)
  rewrite AbsIR_eq_inv_x in HC;[|eauto using 
      shift_zeroR_leEq_minus,
      less_leEq].
  rewrite minusInvR in HC.
  apply (plus_resp_leEq_both _ _ _ _ _ HC) in Hq.
  apply shift_leEq_minus in Hq.
  match type of Hq with
  |?l [<=] _ => remember l as Lhide
  end.
  unfold cg_minus in Hq.
  ring_simplify in Hq.
  rewrite cag_commutes_unfolded  in Hq.
  fold (cg_minus fq ft) in Hq.
  subst Lhide.
  rewrite <- x_plus_x in Hq.
  apply shift_leEq_minus in Hq.
  remember (ft[-]fq) as ftmx.
  apply shift_leEq_minus in Hq.
  rewrite cg_minus_correct in Hq.
  subst ftmx. unfold cg_minus in Hq.
  rewrite cg_inv_inv in Hq.
  ring_simplify in Hq.
  apply leEq_def in Hq.
  unfold Not in Hq. tauto.
Qed.

Lemma ContFunQRLe : forall (f : PartIR)  (a b : Q) (c : IR),
Continuous (clcr a b) f
->(forall (t:Q) pD, ((clcr a b) t) -> (f t pD [<=] c))
-> (forall (t:IR) pD, ((clcr a b) t)-> (f t pD [<=] c)).
Proof.
  intros ? ? ? ? cc Hq ? ? pab.
  rewrite (pfwdef _ _ _ _ pD ((fst cc) _ pab));[|eauto 2 with CoRN].
  apply ContFunQRLeAux.
  intros  q  p.
  specialize (Hq q (fst cc _ p)).
  tauto.
Qed.

Lemma ContFunQRGe : forall (f : PartIR)  (a b : Q) (c : IR),
Continuous (clcr a b) f
->(forall (t:Q) pD, ((clcr a b) t) -> (c [<=] f t pD))
-> (forall (t:IR) pD, ((clcr a b) t)-> (c [<=] f t pD)).
Proof.
  intros ? ? ? ? cc Hq ? ? pab.
  rewrite (pfwdef _ _ _ _ pD ((fst cc) _ pab));[|eauto 2 with CoRN].
  apply ContFunQRGeAux.
  intros  q  p.
  specialize (Hq q (fst cc _ p)).
  tauto.
Qed.

Require Export CoRN.ftc.StrongIVT.

Lemma closeRationalLR : forall (a b x d : IR) (Hab : a [<] b),
  (Compact (less_leEq _ _ _ Hab)) x
  -> [0][<]d
  -> {q : Q | (Compact (less_leEq _ _ _ Hab)) q /\
                      AbsIR (x[-]q)[<=]d}.
Proof.
  intros ? ? ? ? ? Hcc Hdp.
  pose proof Hab as Hap.
  apply less_cotransitive_unfolded with (z:=x)in Hap.
  destruct Hap as [Hlt | Hgt].
- apply closeRationalL; auto.
- apply closeRationalR; auto.
Qed.

(** this lemma is stronger than Weak_IVT. the only change
    is that the type of [x] (in the concluion)
    is Q, instead of IR *)
Lemma Weak_IVTQ
     : forall (I : interval) (F : PartFunct IR),
       Continuous I F ->
       forall (a b : IR) (Ha : Dom F a) (Hb : Dom F b)
         (HFab : F a Ha[<]F b Hb),
       I a ->
       I b ->
       forall e : IR,
       [0][<]e ->
       forall y : IR,
       Compact (less_leEq IR (F a Ha) (F b Hb) HFab) y ->
       {x : Q | Compact (Min_leEq_Max a b) x /\
       forall Hx : Dom F x, AbsIR (F x Hx[-]y)[<=]e}.
Proof.
  intros ? ? Hc ? ? ? ? ? Hia Hib ? He ? Hcp.
  apply pos_div_two in He.
  pose proof He as Hivt.
  eapply Weak_IVT with (y:=y) (F:=F) (HFab := HFab) in Hivt;
    eauto.
  unfold compact in He.
  unfold Continuous in Hc.
  destruct Hc as [Hcl Hcr].
  specialize (Hcr _ _  (Min_leEq_Max a b)).
  unfold Continuous_I in Hcr.
  match type of Hcr with
  ?A -> _ => assert A as H99 by (apply included_interval; auto);
            pose proof (included_trans _ _ _ _ H99 Hcl) as Hdom;
             specialize (Hcr H99); clear H99
  end.

  apply snd in Hcr.
  specialize (Hcr _ He).
  destruct Hcr as [d Hdp Hcc].
  destruct Hivt as [x Hmm Hfx].
  pose proof HFab as Hap.
  specialize (fun xp => Hcc x xp Hmm).
    (* y already names a point in the co-domain *)
  apply less_imp_ap in Hap.
  apply pfstrx in Hap.
  apply ap_imp_Min_less_Max in Hap.
  pose proof (closeRationalLR _ _ _ _ Hap Hmm Hdp) as Hqq.
  destruct Hqq as [q H99].
  exists q.
  destruct H99 as [Hcomp Hab].
  split;[exact Hcomp|].
  specialize (Hcc q Hcomp (Hdom _ Hmm) (Hdom _ Hcomp) Hab).
  specialize (Hfx (Hdom _ Hmm)).
  rewrite AbsIR_minus in Hcc.
  apply AbsIR_imp_AbsSmall in Hcc.
  apply AbsIR_imp_AbsSmall in Hfx.
  pose proof (AbsSmall_eps_div_two  _ _ _ _ Hcc Hfx) as Hsum.
  clear Hfx Hcc.
  unfold cg_minus in Hsum.
  ring_simplify in Hsum.
  intros Hx.
  apply AbsSmall_imp_AbsIR.
  rewrite pfwdef with (Hy := Hx) in Hsum; trivial.
  apply eq_reflexive.
Qed.

Lemma decideEdDN : ∀ (x y : IR), Not (Not (x [=] y or x [#] y)).
Proof.
    intros ? ?.
    pose proof (AbsIR_nonneg (x[-]y)) as Hd.
    apply leEq_less_or_equal in Hd.
    intro Hc.
    apply Hd.
    clear Hd. intro Hd. apply Hc.
    destruct Hd as [Hd | Hd];[right | left].
    - apply pos_ap_zero in Hd.
      apply AbsIR_cancel_ap_zero in Hd.
      apply zero_minus_apart.  exact Hd.
    - symmetry in Hd. apply AbsIR_eq_zero in Hd.
      apply cg_inv_unique_2. exact Hd.
Qed.

Hint Rewrite cg_inv_zero : CoRN.
