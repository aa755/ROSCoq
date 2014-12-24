Require Export CoRN.ftc.Derivative.   
Require Export CoRN.ftc.Integral.
Require Export CoRN.ftc.FTC.


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

Definition LBoundInCompInt {a b} (Hab : a [<]b)
 (F : PartIR) (lb : IR) 
   :=
forall x : IR,
  Compact (less_leEq IR a b Hab) x 
  -> forall Hx : Dom F x, lb [<=] F x Hx.


(** Combines Barrow's theorem ([Barrow2]) and 
    [ub_integral]*)
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

Definition Q2R  (q: Q) : IR := (inj_Q IR q).
Coercion  Q2R : Q >-> st_car.

Require Import Coq.QArith.Qfield.
Require Import Coq.QArith.Qring.
Require Import Psatz.

Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Add Ring IRisaRing: (CRing_Ring IR).
Require Import Psatz.
Require Import Setoid.


Hint Resolve less_leEq_trans leEq_less_trans plus_resp_less_leEq
plus_resp_leEq_less minus_resp_less_leEq plus_resp_pos_nonneg
leEq_inj_Q leEq_wdr leEq_wdr leEq_reflexive eq_imp_leEq
leEq_imp_eq leEq_imp_eq leEq_transitive (leEq_inj_Q IR) less_leEq
Min_leEq_rht Min_leEq_lft
shift_zero_leEq_minus shift_minus_leEq
pos_two: CoRN.

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

Lemma ContFunQRLe : forall (f : PartIR)  (a b : Q) (c : IR)
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
  pose proof (less_Min _ _ _ (ltAddRhs t d Hdp) Hcc) as Hmlt.
  pose proof (Q_dense_in_CReals' _ _ _ Hmlt) as Hqr.
  destruct Hqr as [q Hqr Hql].
  specialize (Hq q).
  simpl in p. unfold Q2R in p. destruct p as [pl pr].
  assert (inj_Q _ a[<=]inj_Q IR q) as Haq by (eauto using
        less_leEq, leEq_less_trans).
  assert (inj_Q IR q[<=] inj_Q _ b) as Hqb by (eauto using
      less_leEq,
      less_leEq_trans,
      Min_leEq_rht).
  
  specialize (Hq (Haq, Hqb)).
  specialize (HC t q).
  unfold compact in HC.
  lapply HC;[clear HC; intro HC|split; auto].
  lapply HC;[clear HC; intro HC|split; auto].
  specialize (HC (HI _ (pl,pr)) (HI _ (Haq, Hqb))).
  rewrite AbsIR_minus in HC. unfold Q2R in HC.
  rewrite AbsIR_eq_x in HC;[|info_eauto 4 using 
        shift_zero_leEq_minus, less_leEq].
  lapply HC;[ clear HC; intro HC | 
    apply shift_minus_leEq;
    rewrite cag_commutes_unfolded; (eauto 4 with CoRN)].
  clear Hql Hqr Hmlt Hcc Hdp.
  subst eps. clear Hc.
  remember (f t (HI t (pl, pr))) as ft.
  clear Heqft. unfold Q2R in Hq.
  remember (f (inj_Q IR q) (HI (inj_Q IR q) (Haq, Hqb))) as fq.
  clear Heqfq.
  apply shift_mult_leEq' in HC; [|eauto 1 with CoRN].
  assert (fq[<]ft) as Hlqt by eauto with CoRN.
  (** Now we need to prove ft[<=]fq *)
  rewrite AbsIR_eq_x in HC;[|eauto with CoRN].
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
