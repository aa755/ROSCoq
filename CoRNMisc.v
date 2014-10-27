
Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
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
