Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.
(** printing ℝ $\mathbb{R}$ #ℝ# *)
(** printing [0] $0$ #0# *)
(** printing [<=] $\le$ #<=# *)

Require Export CoRN.ftc.MoreIntervals.

Notation ℝ := IR.

Require Export Coq.ZArith.ZArith.

Require Export IRMisc.CoRNMisc.

Require Export IRMisc.ContField.

Require Export StdlibMisc.

Definition N2R  (n: nat) : IR := (inj_Q IR  (inject_Z n)).


(** Time is modeled as a real number. One is allowed to make non-deterministic
   decisions on time *)



Notation "a < b < c" := (Qlt a  b /\  Qlt b  c) : Q_scope .


(** CatchFileBetweenTagsStartTime *)
Definition Time := (RInIntvl (closel [0])).
(** CatchFileBetweenTagsEndTime *)


Open Scope Q_scope.



Definition tdiff (t tl : Time) : Time.
(*  exists (Qabs (tl - t)).
  apply Qabs_nonneg. *)

  exists (AbsIR (tl [-] t)).
  unfold iprop. apply AbsIR_nonneg.
Defined.

Hint Resolve plus_resp_nonneg : CoRN. 
 Definition tadd (t tl : Time) : Time.
   exists (t [+] tl).
   unfold iprop. destruct t. destruct tl.
   simpl. 
   eauto using plus_resp_nonneg.

   (*   exists (tl + t). destruct t, tl. simpl.
      apply Q.Qplus_nonneg; auto. 
      *)
 Defined.

 Lemma N2RNonNeg : forall n, [0][<=]N2R n.
 Proof.
   intro n. unfold N2R. rewrite <- inj_Q_Zero.
   apply inj_Q_leEq.
   apply Q.Qle_nat.
 Qed.

Definition N2T (n: nat) : Time.
   exists (N2R n). unfold iprop.
   apply N2RNonNeg.
Defined.


Definition mkTime (t:ℝ) (p: [0] [<=] t) : Time.
  exists t.
  exact p.
Defined.

Definition QNNeg : Type := {q : Q | (if Qlt_le_dec q 0 then False else True) : Prop}.
Definition QTime := QNNeg.

(** if [q] is a closed non-negative rational, then p:=I is guaranteed to work *)
Definition mkQTime (q:Q) (p: (if Qlt_le_dec q 0 then False else True)) : QTime
:= exist _ q p.



Definition QT2Q (t : QTime) : Q := let (x, _) := t in x.


Definition QT2T (q: QTime) : Time.
  destruct q as [q qp].
  exists (Q2R q). simpl.
  unfold Q2R.
  rewrite <- inj_Q_Zero.
  apply inj_Q_leEq. simpl.
  destruct (Qlt_le_dec q 0); auto.
  contradiction.
Defined.

Definition QT2R (q: QTime) : ℝ.
  exact (Q2R (QT2Q q)).
Defined.

Coercion N2T : nat >-> st_car.
  (* Q.Qle_nat *)

Coercion QT2T : QTime >-> st_car.
Coercion QT2Q : QTime >-> Q.


Definition equalUpto {Value : Type} (t: Time) (f1 f2 : Time -> Value) :=
  forall  (ti: Time), (ti [<=] t) -> f1 ti = f2 ti.


Open Scope R_scope.



Require Export CoRN.reals.Q_in_CReals.

Definition Z2R  (n: Z) : ℝ := (inj_Q ℝ  (inject_Z n)).

Definition overApproximate (t: ℝ) : { z:  Z | t  [<] Z2R z}.
  remember (start_of_sequence _ t).
  clear Heqs. destruct s as [qf Hp]. destruct Hp as [qc Hpp].
  exists (Qround.Qceiling qc).
  unfold Z2R. pose proof (Qround.Qle_ceiling qc) as Hq.
  apply (inj_Q_leEq IR) in Hq.
  eauto  using less_leEq_trans.
Defined.


Definition RTime :=Time.



(** Much of the work in defining devices is to decide what the inputs
    and outputs are and what property they specify. Each device is defined
    in it's own file *)

Close Scope R_scope.


(** A [TContR] is a partial function from reals to reals,
   such that its domain includes the non-negative reals.
   From this, one can extract a member of [Time -> R]
   representing how the physical quantity changed over time.
  [PartIR] ensures functionality, unlike  [Time -> R] *)


Definition TContR := (IContR (closel [0])) I.

(* Coercion TContR2Fun : TContR >-> PartFunct. *)
  
Definition isDerivativeOf (F' F : TContR) : CProp :=
  @isIDerivativeOf (closel [0]) I F' F.



Notation "{ f }" := (getF f).


Lemma Qlt_le_decLeft {T} : forall (a b : Q)(x y : T),
   (a <= b) 
  -> (if Qlt_le_dec b a then x else y) =y.
Proof.
  intros ? ? ? ?  Hlt.
  destruct (Qlt_le_dec b a); [|reflexivity].
  apply Qlt_not_le in q.
  tauto.
Defined.


Definition mkQTimeSnd  (t : Q ) (p: 0 <= t) : 
    (if Qlt_le_dec t 0 then False else True).
Proof.
  intros. rewrite Qlt_le_decLeft; trivial.
Defined.

Definition QTimeD {t : Q} (tp : (if Qlt_le_dec t 0 then False else True)) 
    : 0<= t .
  destruct (Qlt_le_dec t 0);[contradiction| trivial].
Defined.


Definition mkQTime1  (t : Q) (tl: QTime) (p: tl <= t) : QTime.
  exists t.
  apply mkQTimeSnd.
  destruct tl as [tq tp].
  simpl in p.
  apply QTimeD in tp.
  eauto using Qle_trans.
Defined.

Definition mkQTimeT  (t : Q) (tl: Time) (p: tl [<=] t) : QTime.
  exists t.
  apply mkQTimeSnd.
  destruct tl as [tq tp].
  simpl in p.
  simpl in tp.
  apply (leEq_inj_Q IR).
  rewrite inj_Q_Zero.
  eauto using leEq_transitive.
Defined.

Definition mkQTimeInj  (t : Q) (tl: QTime) (p: Q2R tl [<=] Q2R t) : QTime.
  eapply mkQTime1.
  apply leEq_inj_Q in p.
  apply p.
Defined.


Lemma timeIncludedQ : forall (ta tb : QTime),
  included (clcr (QT2Q ta) (QT2Q tb)) (closel [0]).
Proof.
  destruct ta as [ra pa].
  destruct tb as [rb pb].
  simpl. simpl in pa. simpl in pb.
  unfold included. intros ? Hlft.
  simpl in Hlft.
  destruct Hlft. simpl.
  apply QTimeD in pa.
  apply QTimeD in pb.
  apply (inj_Q_leEq IR) in pa.
  rewrite inj_Q_Zero in pa.
  eauto using leEq_transitive.
Qed.


Lemma getFToPart (f : TContR) : forall (t : Time),
  ({f}  t) [=] (toPart f) t (scs_prf _ _ t).
Proof.
  intros ?.
  apply   extToPart3.
Qed.

Lemma getFToPart2 (f : TContR) : forall (t : IR) 
  (p : Dom (toPart f) t), (toPart f) t p [=] {f} (mkTime t p).
Proof.
  intros ? ?. symmetry.
  destruct f.
  simpl.
  apply   extToPart.
Qed.

Lemma TDerivativeUB :forall {F F' : TContR}
   (ta tb : Time) (Hab : ta[<]tb) (c : ℝ),
   isDerivativeOf F' F
   -> UBoundInCompInt Hab (toPart F') c
   -> ({F} tb [-] ({F} ta))[<=]c[*](tb[-]ta).
Proof.
 intros ? ? ? ? ? ? Hisd Hub.
 rewrite getFToPart.
 rewrite getFToPart.
 apply (AntiderivativeUB2 (toPart F) (toPart F') ta tb Hab); auto.
 unfold isDerivativeOf, isIDerivativeOf in Hisd.
 apply Included_imp_Derivative with 
   (I:=closel [0]) (pI := I); trivial;[].
 apply intvlIncluded.
Qed.

Lemma TDerivativeLB :forall {F F' : TContR}
   (ta tb : Time) (Hab : ta[<]tb) (c : ℝ),
   isDerivativeOf F' F
   -> LBoundInCompInt Hab (toPart F') c
   -> c[*](tb[-]ta) [<=] ((getF F) tb[-] (getF F) ta).
Proof.
 intros ? ? ? ? ? ? Hisd Hub.
 rewrite getFToPart.
 rewrite getFToPart.
 apply (AntiderivativeLB2 (toPart F) (toPart F') ta tb Hab); auto.
 unfold isDerivativeOf in Hisd.
 apply Included_imp_Derivative with 
   (I:=closel [0]) (pI := I); trivial;[].
 apply intvlIncluded.
Qed.

Definition toTime (t : Time) (r : ℝ) (p :t[<=]r) : Time.
Proof.
  exists r.
  destruct t as [rt  pt].
  simpl in pt.
  simpl.
  eauto using leEq_transitive.
Defined.


Lemma TDerivativeUB2 :forall (F F' : TContR)
   (ta tb : Time) (Hab : ta[<]tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:Time), (clcr ta tb) t -> ({F'} t) [<=] c)
   -> ({F} tb[-] {F} ta)[<=]c[*](tb[-]ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  eapply TDerivativeUB with (Hab0 := Hab); eauto;[].
  unfold UBoundInCompInt.
  intros r Hc ?. unfold compact in Hc.
  destruct Hc as [Hca Hcb].
  
  specialize (Hub (toTime _ _ Hca)).
  rewrite <- extToPart2.
  unfold getF in Hub.
  assert ((toTime ta r Hca) [=] (mkRIntvl (closel [0]) r Hx)) as Heq
    by (simpl; apply eq_reflexive).
  rewrite <- Heq.
  apply Hub.
  split; auto.
Qed.

Lemma TDerivativeLB2 :forall (F F' : TContR)
   (ta tb : Time) (Hab : ta[<]tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:Time), (clcr ta tb) t -> c [<=] ({F'} t))
   -> c[*](tb[-]ta) [<=] ({F} tb[-] {F} ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  eapply TDerivativeLB with (Hab0 := Hab); eauto;[].
  unfold UBoundInCompInt.
  intros r Hc ?. unfold compact in Hc.
  unfold getF in Hub.
  destruct Hc as [Hca Hcb].
  specialize (Hub (toTime _ _ Hca)).
  rewrite <- extToPart2.
  unfold getF in Hub.
  assert ((toTime ta r Hca) [=] (mkRIntvl (closel [0]) r Hx)) as Heq
    by (simpl; apply eq_reflexive).
  rewrite <- Heq.
  apply Hub.
  split; auto.
Qed.

Definition opBind {A B : Type}
  (f : A-> option B) (a : option A) : option B :=
match a with
| Some a' => f a'
| None => None
end. 

Definition opBind2 {A B : Type}
  (f : A-> B) (a : option A) : option B :=
match a with
| Some a' => Some (f a')
| None => None
end. 

Definition opExtract {A : Type}
   (a : option A) (def: A ): A :=
match a with
| Some a' => a'
| None => def
end.

Definition op2List {A} (a : option A) : list A :=
match a with
| Some a' => cons (a') nil
| None => nil
end.


Definition opApPure {A B : Type}
  (f : A-> B) (def : B) (a : option A) 
  : B :=
match a with
| Some a' => f a'
| None => def
end.

Definition opLiftF {A : Type}
  (f : A-> Prop) (a : option A) 
  : Prop := opApPure f False a.

Definition nextInterval (tstart : QTime) 
    (nextMesgTime : option QTime) : interval :=
match nextMesgTime with
| Some tm => clcr (QT2R tstart) (QT2R tm)
| None => closel (QT2R tstart)
end.


Definition nbdAround ( radius center : ℝ) :=
clcr (radius [-] center) (radius [+] center).

Ltac parallelExist Hyp :=
      match type of Hyp with
      | exists _ : ?A, _   =>
            match goal with
            [ |- exists _ : A, _] =>
              let xx := fresh "x" in
              destruct Hyp as [xx Hyp]; exists xx
             end
      end.

Ltac parallelForall Hyp :=
      match type of Hyp with
      | forall _ : ?A, _   =>
            match goal with
            [ |- forall _ : A, _] =>
              let xx := fresh "x" in
              intro xx; specialize (Hyp xx)
             end
      end.

Ltac Parallel Hyp := 
  repeat progress (parallelForall Hyp || parallelExist Hyp).

Require Import Coq.QArith.Qfield.
Require Import Coq.QArith.Qring.
Require Import Psatz.

Lemma qSubLt : forall (qa qb diff: Q), 
  qa < qb + diff
  -> qa - qb < diff.
Proof.
  intros ? ? ? Hsendlrrr.
  lra.
Qed.

Lemma realCancel : forall (R: CReals) (cpvt cpst : R), 
      (cpst[+](cpvt[-]cpst) [=] cpvt).
Proof.
  intros.
  rewrite cg_minus_unfolded.
  rewrite cag_commutes.
  rewrite <- CSemiGroups.plus_assoc.
  rewrite (cag_commutes _ ([--]cpst) cpst).
  rewrite  CSemiGroups.plus_assoc.
  rewrite <- cg_minus_unfolded.
  rewrite grp_inv_assoc.
  reflexivity.
Qed.

Hint Rewrite realCancel : CoRN.



Ltac TrimAndRHS Hyp :=
let H99 := fresh "H99" in 
destruct Hyp as [Hyp H99]; clear H99.

Ltac TrimAndLHS Hyp :=
let H99 := fresh "H99" in 
destruct Hyp as [H99 Hyp]; clear H99.
  
Definition subset {A} (la lb : list A) : Prop :=
  forall a:A, In a la -> In a lb.

Require Import Coq.Logic.Eqdep_dec.

Lemma UIPReflDeq: forall { A : Type} (deq : DecEq A)
  (a: A) (p: a=a), p= eq_refl.
Proof.
  intros.
  remember (@eq_refl A a) as eqr.
  apply UIP_dec.
  destruct deq. auto.
Qed.

Ltac exrepd :=
   repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : prod _ _ |- _ ] => destruct H
           | [ H : exists v : _,_ |- _ ] =>
               let name := fresh v in
               let Hname := fresh v in
               destruct H as [name Hname]
           | [ H : { v : _ | _ } |- _ ] =>
               let name := fresh v in
               let Hname := fresh v in
               destruct H as [name Hname]
           | [ H : { v : _ | _ & _ } |- _ ] =>
               let name := fresh v in
               let Hname := fresh v in
               destruct H as [name Hname]
         end.


Definition inBetween (l m r: Q) := l < m < r.

Lemma inBetweenFold : forall (l m r: Q),
   l < m < r <-> (inBetween l m r).
Proof. intros. reflexivity.
Qed.





Lemma Q2RClCr : forall (a b c : Q), 
  (clcr a c) b
  -> a <= b <=c.
Proof.
  intros ? ? ? pr.
  simpl in pr.
  destruct pr as [pl pr].
  split; apply (leEq_inj_Q IR); trivial.
Defined.

Lemma contTfQ : forall (tf : TContR) (ta tb : QTime), 
    Continuous  (clcr (QT2Q ta) (QT2Q tb)) (toPart tf).
Proof.
  intros ? ? ?.
  pose proof (scs_prf _ _ tf) as Hc.
  simpl in Hc.
  eapply Included_imp_Continuous; eauto.
  apply timeIncludedQ.
Qed.


Lemma TContRExtQ : forall (f : TContR) (a b : QTime),
  a = b -> {f} a [=] {f} b.
Proof.
  intros ? ? ? H.
  unfold getF. rewrite H.
  apply eq_reflexive.
Qed.

Lemma TContRExtQ2 : forall (f : TContR) (a b : QTime),
  inj_Q IR (QT2Q a) [=] inj_Q IR (QT2Q b) -> {f} a [=] {f} b.
Proof.
  intros ? ? ? H.
  unfold getF. apply TContRExt. simpl. destruct a. destruct b.
  simpl. simpl in H.
  auto.
Qed.

Lemma TContRR2QCompactIntUB : forall (tf : TContR)  (ta tb : QTime) (c : IR),
(forall (t:QTime), (ta <= t <= tb) -> ((getF tf) ( t)) [<=] c)
-> (forall (t:Time), ((clcr (QT2Q ta) (QT2Q tb)) t) -> ({tf} t) [<=] c).
Proof.
  intros ? ? ? ? Hq ? Hint.
  rewrite getFToPart.
  apply ContFunQRLe with (a:=ta) (b:=tb); trivial;
  [apply contTfQ|].
  intros tq ? pp.
  specialize (Hq (mkQTimeInj _ _ (fst pp))).
  specialize (Hq (Q2RClCr _ _ _ pp)).
  rewrite  getFToPart2.
  erewrite  csf_fun_wd;[apply Hq|simpl; apply eq_reflexive].
  Qed.


  Hint Rewrite <- inj_Q_One : QSimpl.
  Hint Rewrite <- inj_Q_inv : QSimpl.
  Hint Rewrite <- inj_Q_plus : QSimpl.
  Hint Rewrite <- inj_Q_minus : QSimpl.
  Hint Rewrite <- inj_Q_inv : QSimpl.

Ltac simplInjQ :=
  unfold Q2R, Z2R; autorewrite with QSimpl;
let H99 := fresh "HSimplInjQ" in
match goal with
[|- context [inj_Q _ ?q]] => let qs := eval compute in q in
                         assert (q = qs) as H99 by reflexivity;
                         rewrite H99; clear H99
end.
Ltac UnfoldLRA :=
   (unfold Q2R, Z2R, inject_Z; 
      try apply inj_Q_leEq; 
      try apply inj_Q_less; 
      simpl; lra).

Lemma QT2T_Q2R : forall (qt:QTime),
  inj_Q IR (QT2Q qt) =  (QT2T qt).
Proof.
  intros. destruct qt as [q p].
  unfold QT2T, QT2Q, QT2R.
  simpl. reflexivity.
Qed.

Lemma timeNonNeg: forall t:Time, 
  (closel [0]) t.
Proof.
  intros. destruct t. simpl. trivial.
Qed.

Lemma timeNonNegUnfolded: forall t:Time, 
  [0] [<=] t.
Proof.
  intros. destruct t. simpl. trivial.
Qed.
Hint Immediate timeNonNeg timeNonNegUnfolded: ROSCOQ.

Lemma TContRR2QUB : forall (tf : TContR) (c : ℝ),
(forall (t:QTime), ({tf} t) [<=] c)
-> (forall (t:Time), ({tf} t) [<=] c).
Proof.
  intros ? ? Hq ?.
  pose proof (less_plusOne _ t) as Hl.
  apply Q_dense_in_CReals' in Hl.
  destruct Hl as [q  Htq Hqt].
  apply less_leEq in Htq.
  apply TContRR2QCompactIntUB with (ta:= mkQTime 0 I) 
        (tb:=mkQTimeT q _ Htq); trivial.
  trivial. simplInjQ.
  split;[rewrite inj_Q_Zero|]; simpl; auto.
  eauto with ROSCOQ.
Qed.

Lemma TContRR2QCompactIntLB : forall (tf : TContR)  (ta tb : QTime) (c : ℝ),
(forall (t:QTime), (ta <= t <= tb) -> c [<=] ({tf} t))
-> (forall (t:Time), ((clcr (QT2Q ta) (QT2Q tb)) t) -> c [<=] ({tf} t)).
Proof.
  intros ? ? ? ? Hq ? Hint.
  rewrite  getFToPart.
  apply ContFunQRGe with (a:=ta) (b:=tb); trivial;
  [apply contTfQ|].
  intros tq ? pp.
  specialize (Hq (mkQTimeInj _ _ (fst pp))).
  specialize (Hq (Q2RClCr _ _ _ pp)).
  rewrite  getFToPart2.
  erewrite  csf_fun_wd;[apply Hq|simpl; apply eq_reflexive].
Qed.

Lemma TContRR2QLB : forall (tf : TContR) (c : ℝ),
(forall (t:QTime),  c [<=] ({tf} t))
-> (forall (t:Time), c [<=] ({tf} t)).
Proof.
  intros ? ? Hq ?.
  pose proof (less_plusOne _ t) as Hl.
  apply Q_dense_in_CReals' in Hl.
  destruct Hl as [q  Htq Hqt].
  apply less_leEq in Htq.
  apply TContRR2QCompactIntLB with (ta:= mkQTime 0 I) 
        (tb:=mkQTimeT q _ Htq); trivial.
  trivial. simplInjQ.
  split;[rewrite inj_Q_Zero|]; simpl; auto.
  eauto with ROSCOQ.
Qed.

Lemma TDerivativeUBQ :forall (F F' : TContR)
   (ta tb : QTime) (Hab : ta <= tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:QTime), ta <= t <= tb -> ({F'} t) [<=] c)
   -> ({F} tb[-] {F} ta)[<=]c[*](tb-ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  apply Qle_lteq in Hab.
  destruct Hab as [Hlt| Heq].
- unfold Q2R. rewrite inj_Q_minus.
  rewrite QT2T_Q2R.
  rewrite QT2T_Q2R.
  eapply TDerivativeUB2; eauto;
    [ rewrite <- QT2T_Q2R;
      rewrite <- QT2T_Q2R;
      apply inj_Q_less; trivial|].
  rewrite <- QT2T_Q2R.
  rewrite <- QT2T_Q2R.
  apply TContRR2QCompactIntUB.
  trivial.
- symmetry in Heq. apply (inj_Q_wd IR) in Heq.
  unfold Q2R. rewrite inj_Q_minus.
  rewrite x_minus_x;
    [rewrite x_minus_x; trivial|];
    [rewrite cring_mult_zero; apply leEq_reflexive|].
  apply  csf_fun_wd.

   rewrite QT2T_Q2R in Heq. rewrite  QT2T_Q2R in Heq. simpl. 
    destruct ta. destruct tb. simpl. apply Heq.
Qed.

Lemma TDerivativeLBQ :forall (F F' : TContR)
   (ta tb : QTime) (Hab : ta <= tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:QTime), ta <= t <= tb -> c [<=] ({F'} t))
   -> c[*](tb-ta)[<=]({F} tb[-] {F} ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  apply Qle_lteq in Hab.
  destruct Hab as [Hlt| Heq].
- unfold Q2R. rewrite inj_Q_minus.
  rewrite QT2T_Q2R.
  rewrite QT2T_Q2R.
  eapply TDerivativeLB2; eauto;
    [ rewrite <- QT2T_Q2R;
      rewrite <- QT2T_Q2R;
      apply inj_Q_less; trivial|].
  rewrite <- QT2T_Q2R.
  rewrite <- QT2T_Q2R.
  apply TContRR2QCompactIntLB.
  trivial.
- symmetry in Heq. apply (inj_Q_wd IR) in Heq.
  unfold Q2R. rewrite inj_Q_minus.
  rewrite x_minus_x;
    [rewrite x_minus_x|]; trivial;
    [rewrite cring_mult_zero; apply leEq_reflexive|].
  apply  csf_fun_wd.

   rewrite QT2T_Q2R in Heq. rewrite  QT2T_Q2R in Heq. simpl. 
    destruct ta. destruct tb. simpl. apply Heq.
Qed.

Ltac AndProjNAux n H :=
match n with
| O => try (apply proj1 in H)
| S ?n' =>  apply proj2 in H; AndProjNAux n' H
end.

Tactic Notation "AndProjN" constr(n) ident(H) "as " ident(Hn) :=
  pose proof H as Hn;
  AndProjNAux n  Hn.

Lemma qtimePos : forall t:QTime, 0 <= t.
Proof.
  intros t. destruct t. simpl.
  apply QTimeD. trivial.
Qed.

Definition notNone {T : Type} (op : option T) : bool :=
match op with
| Some _ => true
| None => false
end.

Lemma mapNil {A B}: forall f : A->B, 
    map f nil = nil.
intros. reflexivity.
Qed.

Lemma AbsIR_ABSIR: forall x, ABSIR x = AbsIR x.
  intros. reflexivity.
Qed.

Lemma IVTTimeMinMax: forall (F : TContR) (ta tb : Time) (e y : IR),
   ({F} ta[<]{F} tb)
   -> [0][<]e 
   -> (clcr ({F} ta) ({F} tb)) y 
   -> {x : QTime | (clcr (Min ta tb) (Max ta tb)) (QT2Q x) ×
                    AbsIR ({F} x [-]y)[<=]e}.
Proof.
  intros ? ? ? ? ?.
  intros Hflt He Hy. simpl in Hy. 
  apply extToPartLt2 in Hflt.
  destruct F.
  simpl. simpl in Hy. simpl in Hflt.
  eapply Weak_IVTQ with (y:=y) (F:= (toPart scs_elem)) (HFab := Hflt) in He; 
    eauto 1 with ROSCOQ;
    [|destruct ta; destruct tb; exact Hy].
  destruct He as [t H99]. destruct H99 as [He Ha].
  unfold compact in He.
  pose proof (leEq_Min _ _ _ (timeNonNeg ta) (timeNonNeg tb)) as HH.
  destruct He as [Hel Her].
  pose proof Hel as Helb.
  eapply leEq_transitive in Hel;[|apply HH].
  unfold Q2R in Hel.
  rewrite <- inj_Q_Zero in Hel.
  apply leEq_inj_Q in Hel.
  simpl in Hel.
  apply mkQTimeSnd in Hel.
  exists (mkQTime _ Hel).
  rewrite AbsIR_ABSIR.
  dands; auto.
  rewrite extToPart3; auto.
Qed.
  

(*
Lemma contITf : forall (tf : TContR) (ta tb : Time), 
    Continuous_I  (Min_leEq_Max ta tb) (toPart tf).
Proof.
  intros ? ? ?.
  apply (contTf tf (TMin ta tb) (TMax ta tb)).
  unfold compact.
  simpl. intros ? Hc.
  simpl. trivial.
Qed.
*)

(*
Lemma  ContinTFSimpl : 
   forall (F : TContR) (ta tb : Time) (e  : IR),
      [0][<]e ->
      {d : IR | [0][<]d |
      forall x y : Time,
      Compact (Min_leEq_Max ta tb) x ->
      Compact (Min_leEq_Max ta tb) y ->
      AbsIR (x[-]y)[<=]d -> AbsIR ({F} x[-]{F} y)[<=]e}.
Proof.
  intros ? ? ? ? Hgt.
  pose proof (contITf F ta tb) as Hc.
  apply snd in Hc.
  specialize (Hc _ Hgt).
  destruct Hc as [d Hdgt Hcn].
  exists d; eauto.
Qed.
*)

Lemma MinTAdd : forall (tx ty : Time),
  MIN tx (tx[+]ty) [=] tx.
Proof.
  intros.
  apply leEq_imp_Min_is_lft.
  rewrite cag_commutes.
  apply shift_leEq_plus.
  rewrite cg_minus_correct.
  eauto 1  with ROSCOQ.
Qed.

Lemma MaxTAdd : forall (tx ty : Time),
  MAX tx (tx[+]ty) [=] (tx[+]ty).
Proof.
  intros.
  apply leEq_imp_Max_is_rht.
  rewrite cag_commutes.
  apply shift_leEq_plus.
  rewrite cg_minus_correct.
  eauto 1  with ROSCOQ.
Qed.

Lemma injQGt0 : forall q:Q, 0 < q ->  [0][<] inj_Q IR q.
  intros ? Hq.
  eapply less_wdl;[| apply inj_Q_Zero].
  apply inj_Q_less.
  trivial.
Qed.

Lemma QT2TGt0 : forall q:QTime, 0 < q ->  [0][<] QT2T q.
  intros ? Hq.
  destruct q as [q qp]. simpl.
  simpl in Hq.
  apply injQGt0.
  trivial.
Qed.
  
Definition mkQTimeLt  (t : Q) (tl: Time) (p: tl [<] t) : QTime.
  exists t.
  apply mkQTimeSnd.
  apply (leEq_inj_Q IR).
  rewrite inj_Q_Zero.
  unfold Q2R in p.
  eauto using timeNonNegUnfolded, leEq_less_trans, less_leEq.
Defined.

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

Lemma TContRlt:  forall (p : TContR) x y,
        {p} x [<]{p} y 
        -> x[<=]y
        -> x[<]y.
Proof.
  intros ? ? ? Hpp Hle.
  apply extToPartLt2 in Hpp.
  apply pfstrlt in Hpp; auto.
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

Lemma TContRgt:  forall (p : TContR) x y,
        {p} x [<]{p} y 
        -> y[<=]x
        -> y[<]x.
Proof.
  intros ? ? ? Hpp Hle.
  apply extToPartLt2 in Hpp.
  apply pfstrgt in Hpp; auto.
Qed.

Ltac provefalse :=
  assert False ;[| contradiction].

Lemma minusInvQ : forall a b:Q, [--](a[-]b)[=](b[-]a).
Proof.
  intros. unfold cg_minus.
  simpl. ring.
Qed.


 Definition Qtadd (t tl : QTime) : QTime.
  exists (t + tl).
  destruct t as [qt qp].
  destruct tl as [qlt qlp].
  simpl.
  apply mkQTimeSnd.
  apply QTimeD in qlp.
  apply QTimeD in qp.
  lra.
Defined.

Ltac DestImp H :=
 lapply H;[clear H; intro H|].

Definition between (b a c : IR) 
  := ((Min a c [<=] b) /\ (b [<=] Max a c)) .

Definition changesTo (f : TContR)
  (atTime uptoTime : QTime)
  (toValue : ℝ)
  (reactionTime eps : Q) :=
(exists  (qt : QTime), 
  atTime <= qt <= (atTime + reactionTime)
  /\ ((forall t : QTime, 
          (qt <= t <= uptoTime -> AbsIR ({f} t [-] toValue) [<=] eps)))
  /\ (forall t : QTime, (atTime <= t <= qt)  
          -> (between ({f} t) ({f} atTime) toValue)))%Q.

Require Export Coq.Unicode.Utf8.

Instance TContR_proper (f : TContR) :
  Proper ((fun (x y : QTime) => Qeq x y) ==> (@st_eq IR)) (fun (q : QTime) => {f} q).
Proof.
  intros ? ? Heq. apply  csf_fun_wd. unfold Basics.flip in Heq.
  destruct x,y. simpl. simpl in Heq. apply inj_Q_wd. exact Heq.
Qed.


Hint Rewrite Max_id  Min_id cring_mult_zero_op : CoRN.

Lemma TDerivativeEqQ :forall (F F' : TContR)
   (ta tb : QTime) (Hab : ta <= tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:QTime), ta <= t <= tb -> ({F'} t) [=] c)
   -> ({F} tb[-] {F} ta)[=]c[*](tb-ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  apply leEq_imp_eq;
    [apply TDerivativeUBQ with (F':=F') | apply TDerivativeLBQ with (F':=F')]; 
      auto; intros ? Hbw; rewrite (Hub _ Hbw); apply leEq_reflexive.
Qed.

Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Add Ring RisaRing: (CRing_Ring IR).

Ltac IRRing :=
  unfold cg_minus; ring; idtac "ring failed; try unfolding
   definitions to make the ring structure visible, Also note
    that ring does not look at Hypothesis".
    
Lemma TDerivativeEqQ0 :forall (F F' : TContR)
   (ta tb : QTime) (Hab : ta <= tb),
   isDerivativeOf F' F
   -> (forall (t:QTime), ta <= t <= tb -> ({F'} t) [=] [0])
   -> ({F} tb[=] {F} ta).
Proof.
  intros ? ?  ? ? ? Hder Hub.
  eapply TDerivativeEqQ in Hub; eauto.
  rewrite cring_mult_zero_op in Hub.
  remember ({F} ta) as fta.
  remember ({F} tb) as ftb.
  assert (fta[=]fta [+] [0]) as H by ring.
  rewrite H.
  rewrite <- Hub. unfold cg_minus. IRRing.
Qed.

Ltac Dor H := destruct H as [H|H].

(** often a better way to prove conjumction*)
Lemma BetterConj : ∀ (A B : Prop),
  A -> (A -> B) -> (A /\ B).
tauto.
Qed.


Lemma changesToDeriv0Deriv :  ∀ (F': TContR)
  (atTime uptoTime : QTime)
  (reactionTime : Q),
  atTime <= uptoTime
  → changesTo F' atTime uptoTime 0 reactionTime 0
  → {F'} atTime [=] 0 
  → ∀ (t : QTime), atTime <= t <= uptoTime 
      → {F'} t [=] 0.
Proof.
  intros ? ? ? ? Hle Hc Hf0.
  unfold changesTo in Hc.
  destruct Hc as [qtrans  Hm]. repnd.
  pose proof (Q_dec atTime uptoTime) as Htric.
  intros ? Hbw.
  destruct Htric as [Htric | Htric];
    [|rewrite <- Hf0;
      apply TContR_proper;auto; simpl; lra; fail].
  destruct Htric as [Htric | Htric] ;[|lra].
  assert (proper (clcr (QT2Q atTime) (QT2Q uptoTime))) as pJ by UnfoldLRA.
  unfold between in Hmrr.
  setoid_rewrite Hf0 in Hmrr.
  setoid_rewrite  Max_id  in Hmrr.
  setoid_rewrite  Min_id  in Hmrr. repnd.
  rename t into qt.
  pose proof (Qlt_le_dec qt qtrans) as Hdec.
  Dor Hdec;[clear Hmrl | clear Hmrr].
- apply Qlt_le_weak in Hdec.
  specialize (Hmrr qt (conj Hbwl Hdec)). unfold Q2R in Hmrr.
  rewrite inj_Q_Zero in Hmrr. repnd.
  unfold Q2R. rewrite inj_Q_Zero.
  apply leEq_imp_eq; assumption.
- assert (qt <= uptoTime) as Hup by lra.
  specialize (Hmrl qt (conj Hdec Hup)).
  apply AbsIR_imp_AbsSmall in Hmrl.
  unfold AbsSmall in Hmrl.
  unfold Q2R in Hmrl.
  rewrite inj_Q_Zero, cg_zero_inv, cg_inv_zero in Hmrl. repnd.
  unfold Q2R. rewrite inj_Q_Zero.
  apply leEq_imp_eq; assumption.
Qed.
  
Lemma changesToDeriv0Integ :  ∀ (F' F: TContR)
  (atTime uptoTime : QTime)
  (reactionTime : Q),
  atTime <= uptoTime
  → changesTo F' atTime uptoTime 0 reactionTime 0
  → {F'} atTime [=] 0 
  → isDerivativeOf F' F
  → ∀ (t : QTime), atTime <= t <= uptoTime 
      → {F} t [=] {F} atTime.
Proof.
  intros ? ? ? ? ? Hle Hc Hf0 Hd.
  pose proof (Q_dec atTime uptoTime) as Htric.
  intros ? Hbw.
  destruct Htric as [Htric | Htric];
    [|apply TContR_proper;auto; simpl; lra; fail].
  destruct Htric as [Htric | Htric] ;[|lra]. 
  apply TDerivativeEqQ0 with (F':=F');try tauto.
  repnd. 
  intros ? Hlt. simpl. remember ({F'} t0) as xx.
  rewrite <- (inj_Q_Zero IR). subst xx.
  eapply changesToDeriv0Deriv in Hc; eauto.
  repnd. split; lra.
Qed.

Lemma changesToDeriv0Comb :  ∀ (F' F: TContR)
  (atTime uptoTime : QTime)
  (reactionTime : Q),
  atTime <= uptoTime
  → changesTo F' atTime uptoTime 0 reactionTime 0
  → {F'} atTime [=] 0 
  → isDerivativeOf F' F
  → ∀ (t : QTime), atTime <= t <= uptoTime 
      → ({F'} t [=] 0 ∧ {F} t [=] {F} atTime).
Proof.
  split;
  eauto using changesToDeriv0Integ, changesToDeriv0Deriv.
Qed.

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


Lemma TDerivativeAbsQ :forall (F F' : TContR)
   (ta tb : QTime) (Hab : ta <= tb) (c eps: ℝ),
   isDerivativeOf F' F
   -> (forall (t:QTime), ta <= t <= tb -> AbsIR ({F'} t [-] c) [<=] eps)
   -> AbsIR({F} tb[-] {F} ta [-] c[*](tb-ta)) [<=] eps [*] (tb - ta).
Proof.
  intros ? ? ? ? ? ? ? Hder Habs.
  pose proof (λ t p, (AbsMinusUB _ _ _ (Habs t p))) as Hub.
  pose proof (λ t p, (AbsMinusLB _ _ _ (Habs t p))) as Hlb.
  clear Habs.
  apply AbsSmall_imp_AbsIR.
  unfold AbsSmall.
  apply TDerivativeUBQ with (F:=F) in Hub; auto.
  apply TDerivativeLBQ with (F:=F) in Hlb; auto.
  clear Hder.
  split;[clear Hub | clear Hlb].
- apply shift_leEq_minus'.
  eapply leEq_transitive;[| apply Hlb].
  apply eqImpliesLeEq.
  unfold Q2R.
  remember (inj_Q IR (tb - ta)) as ba.
  IRRing.
- apply shift_minus_leEq.
  eapply leEq_transitive;[apply Hub|].
  apply eqImpliesLeEq.
  unfold Q2R.
  remember (inj_Q IR (tb - ta)) as ba.
  IRRing.
Qed.

Lemma  triangleMiddle : 
∀ y x z: ℝ, 
  AbsIR (x[-]z)[<=]AbsIR (x [-] y)
                  [+]AbsIR (y [-] z).
  intros.
  assert (x[-]z [=] (x [-] y) [+](y [-] z)) as Hm
    by IRRing.
  rewrite Hm.
  apply triangle_IR.
Qed.


Lemma betweenRAbs : ∀ (b a c : IR),
  between b a c
  -> AbsIR (b[-]c) [<=] AbsIR (a[-]c).
Proof.
  intros ? ? ? Hb.
  unfold between in Hb.
  rewrite (Abs_Max).
  rewrite (Abs_Max).
  repnd.
  apply minus_resp_leEq_both.
- apply Max_leEq; eauto 2 with CoRN.
- apply leEq_Min; eauto 2 with CoRN.
Qed.

(** Exact same proof as above *)  
Lemma betweenLAbs : ∀ (b a c : IR),
  between b a c
  -> AbsIR (b[-]a) [<=] AbsIR (a[-]c).
Proof.
  intros ? ? ? Hb.
  unfold between in Hb.
  rewrite (Abs_Max).
  rewrite (Abs_Max).
  repnd.
  apply minus_resp_leEq_both.
- apply Max_leEq; eauto 2 with CoRN.
- apply leEq_Min; eauto 2 with CoRN.
Qed.


Lemma changesToDerivInteg :  ∀ (F' F: TContR)
  (atTime uptoTime reacTime : QTime) (oldVal newVal : IR)
  ( eps : Q),
  atTime + reacTime < uptoTime
  → changesTo F' atTime uptoTime newVal reacTime eps
  → {F'} atTime [=] oldVal 
  → isDerivativeOf F' F
  → let eps1 := (AbsIR ({F'} atTime[-]newVal)) in
    exists qtrans : QTime,  atTime <= qtrans <= atTime + reacTime
      ∧  AbsIR({F} uptoTime[-]{F} atTime[-]newVal[*](uptoTime - atTime))
          [<=] eps1[*](qtrans - atTime) [+] eps[*](uptoTime - qtrans).
Proof.
  intros ? ? ? ? ? ? ? ? Hr Hc Hf0 Hd eps1.
  pose proof (Q_dec atTime uptoTime) as Htric.
  pose proof (qtimePos reacTime).
  destruct Htric as [Htric | Htric];[|lra].
  destruct Htric as [Htric | Htric] ;[|lra].
  unfold changesTo in Hc.
  destruct Hc as [qtrans  Hm].
  exists qtrans.
  split;[tauto|]. repnd.
  pose proof (λ t p, (betweenRAbs _ _ _ (Hmrr t p)))
     as Hqt. clear Hmrr.
  fold eps1 in Hqt.
  apply TDerivativeAbsQ with (F:=F) in Hqt;[|auto|auto].
  apply TDerivativeAbsQ with (F:=F) in Hmrl;[|lra|auto].
  pose proof (plus_resp_leEq_both _ _ _ _ _ Hqt Hmrl) as Hp.
  eapply leEq_transitive in Hp;[| apply triangle_IR].
  unfold Q2R.
  rewrite inj_Q_mult.
  eapply leEq_transitive;[| apply Hp].
  apply eqImpliesLeEq.
  apply AbsIR_wd.
  unfold Q2R.
  rewrite inj_Q_minus.
  rewrite inj_Q_minus.
  rewrite inj_Q_minus.
  IRRing.
Qed.

Hint Resolve  AbsIR_nonneg : CoRN.

Hint Resolve qtimePos : ROSCOQ.
 
(** we didn't have a direct handle on [qtrans]
    This spec is more extensional *)
Lemma changesToDerivInteg2 :  ∀ (F' F: TContR)
  (atTime uptoTime reacTime : QTime) (oldVal newVal : IR)
  ( eps : QTime),
  atTime + reacTime < uptoTime
  → changesTo F' atTime uptoTime newVal reacTime eps
  → {F'} atTime [=] oldVal 
  → isDerivativeOf F' F
  → let eps1 := (AbsIR ({F'} atTime[-]newVal)) in
     AbsIR({F} uptoTime[-]{F} atTime[-]newVal[*](uptoTime - atTime))
          [<=] eps1[*](QT2R reacTime) [+]  eps*(uptoTime - atTime).
Proof.
  intros ? ? ? ? ? ? ? ? Hr Hc Hf0 Hd eps1.
  eapply changesToDerivInteg in Hc; eauto.
  destruct Hc as [qtrans Hc].
  repnd.
  eapply leEq_transitive;[apply Hcr|].
  fold (eps1).
  apply plus_resp_leEq_both.
- unfold Q2R.
  destruct reacTime.
  simpl QT2R.
  simpl in Hclr, Hr.
  apply mult_resp_leEq_lft;
    [apply inj_Q_leEq; simpl; lra|].
  subst eps1. apply AbsIR_nonneg.
- unfold Q2R.
  apply inj_Q_leEq. simpl.
  apply Q.Qmult_le_compat_l;[lra|].
  apply qtimePos.
Qed.
Definition TIntgBnds : Type := IntgBnds (closel [0]).

Definition ChangesToIntBnd {atTime uptoTime reacTime : QTime}
  (p: atTime + reacTime < uptoTime) : TIntgBnds.
Admitted.


Lemma changesToIntegral :  ∀ (F': TContR)
  (atTime uptoTime reacTime : QTime) (oldVal newVal : IR)
  ( eps : QTime)
  (p : atTime + reacTime < uptoTime),
  changesTo F' atTime uptoTime newVal reacTime eps
  → {F'} atTime [=] oldVal 
  → let eps1 := (AbsIR ({F'} atTime[-]newVal)) in
     AbsIR((Cintegral (ChangesToIntBnd p) F') [-]newVal[*](uptoTime - atTime))
          [<=] eps1[*](QT2R reacTime) [+]  eps*(uptoTime - atTime).
Proof.
Admitted.


Lemma TContRR2QCompactIntEq:
  ∀ (tf : TContR) (ta tb : QTime) (c : ℝ),
  (∀ t : QTime, ta <= t ∧ t <= tb → {tf} t[=]c)
  → ∀ t : Time, (clcr (QT2R ta) (QT2R tb)) t → {tf} t[=]c.
Proof.
  intros ? ? ? ? Hq ? ?.
  apply leEq_imp_eq.
- eapply TContRR2QCompactIntUB; eauto. intros. rewrite Hq; auto.
    apply leEq_reflexive.
- eapply TContRR2QCompactIntLB; eauto. intros. rewrite Hq; auto.
    apply leEq_reflexive.
Qed.


Lemma TContRR2QCompactIntEq2:
  ∀ (tf : TContR) (ta tb : QTime) (c : ℝ),
  (∀ t : QTime, ta <= t ∧ t <= tb → {tf} t[=]c)
  → ∀ t : Time, ((QT2R ta) [<=] t /\ t [<=] (QT2R tb)) → {tf} t[=]c.
Proof.
  intros. eapply TContRR2QCompactIntEq; eauto.
  repnd.
  simpl. split; auto.
Qed.


  Hint Rewrite  inj_Q_One : InjQDown.
  Hint Rewrite  inj_Q_inv : InjQDown.
  Hint Rewrite  inj_Q_plus : InjQDown.
  Hint Rewrite  inj_Q_minus : InjQDown.
  Hint Rewrite  inj_Q_inv : InjQDown.
  Hint Rewrite  inj_Q_mult : InjQDown.
  Hint Rewrite <-  inj_Q_mult : QSimpl.


Lemma AbsIR_plus : ∀  (e1 e2 x1 x2 : IR),
  AbsIR x1 [<=]  e1
  → AbsIR x2 [<=]  e2 
  → AbsIR (x1[+]x2) [<=] (e1[+]e2).
Proof.
  intros ? ? ? ? H1 H2.
  apply AbsSmall_imp_AbsIR.
  apply AbsSmall_plus;
  apply AbsIR_imp_AbsSmall; assumption.
Qed.


Lemma QmultOverQminusL : ∀ a b c : Q,
  (c * (a - b) == c * a - c * b)%Q.
Proof.
  intros ? ? ?.
  ring.
Qed.

Lemma QabsTime : ∀ (qp: QTime),
   ((Qabs.Qabs qp) == qp)%Q.
  intros.
  destruct qp; simpl.
  apply QTimeD in y.
  rewrite Qabs.Qabs_pos; lra.
Qed.

Lemma squareMinusIR2:
  ∀  (x y : IR), (x[-]y)[^]2 [+]Two[*]x[*]y [=]x[^]2[+]y[^]2.
Proof.
  intros. rewrite square_minus. rewrite <- one_plus_one.
  unfold cg_minus. ring.
Qed.

