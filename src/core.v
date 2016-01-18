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

Require Import IRMisc.LegacyIRRing.

Definition N2R  (n: nat) : IR := (inj_Q IR  (inject_Z n)).



Notation "a < b < c" := (Qlt a  b /\  Qlt b  c) : Q_scope .


(** [Time] is the type of non-negative real numbers. Its definition
   is slightly complicated because it is defined as a Setoid
   to get the equality right *)
Definition Time : CSetoid := (RInIntvl (closel [0])).


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

Definition QNNeg : Type :=
sig (fun q => (if Qlt_le_dec q 0 then False else True)).

Definition QTime := QNNeg.

(** if [q] is a closed non-negative rational, then p:=I is guaranteed to work *)
Definition mkQTime (q:Q) (p: (if Qlt_le_dec q 0 then False else True)) : QTime :=
exist _ q p.



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


Close Scope R_scope.


(** [TContR] is a ring of continuous functions over time.
    It is defined by first using a pointwise ring constructor
    ([FS_as_PointWise_CRing])
    and then a subsetoid ring constructor [SubCRing] *)

Definition TContR : CRing := (IContR (closel [0])) I.

(* Coercion TContR2Fun : TContR >-> PartFunct. *)


(** asserts that [F'] is the constructive derivative of
    [F] w.r.t. [Time *)   
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
  apply IDerivativeUB.
Qed.

Lemma TDerivativeLB :forall {F F' : TContR}
   (ta tb : Time) (Hab : ta[<]tb) (c : ℝ),
   isDerivativeOf F' F
   -> LBoundInCompInt Hab (toPart F') c
   -> c[*](tb[-]ta) [<=] ((getF F) tb[-] (getF F) ta).
Proof.
  apply IDerivativeLB.
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
  apply IDerivativeUB2.
Qed.

Lemma TDerivativeUB3 :forall (F F' : TContR)
   (ta tb : Time) (Hab : ta[<=]tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:Time), (clcr ta tb) t -> ({F'} t) [<=] c)
   -> ({F} tb[-] {F} ta)[<=]c[*](tb[-]ta).
Proof.
  apply IDerivativeUB3.
Qed.

Lemma TDerivativeLB2 :forall (F F' : TContR)
   (ta tb : Time) (Hab : ta[<]tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:Time), (clcr ta tb) t -> c [<=] ({F'} t))
   -> c[*](tb[-]ta) [<=] ({F} tb[-] {F} ta).
Proof.
  apply IDerivativeLB2.
Qed.


(** double negation trick, to strengthen LB2. The hypothesis
ta[<=]tb was ta[<]tb before*)
Lemma TDerivativeLB3 :forall (F F' : TContR)
   (ta tb : Time) (Hab : ta[<=]tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:Time), (clcr ta tb) t -> c [<=] ({F'} t))
   -> c[*](tb[-]ta) [<=] ({F} tb[-] {F} ta).
Proof.
  apply IDerivativeLB3.
Qed.

Definition nonNegDuring (F : TContR) (tstart tend : Time) :=
  forall (t: Time), (tstart [<=] t /\ t [<=] tend) -> [0] [<=] ({F} t).

Definition nonPosDuring (F : TContR) (tstart tend : Time) :=
  forall (t: Time), (tstart [<=] t /\ t [<=] tend) -> ({F} t) [<=] [0].


Definition noSignChangeDuring (F : TContR) (tstart tend : Time) : Prop :=
  nonNegDuring F tstart tend \/  nonPosDuring F tstart tend.

(*
Definition nonDecreasingDuring (F : TContR) (tstart tend : Time) :=
  forall (ta tb: Time), (tstart [<=] ta /\ ta [<=] tb /\ tb [<=] tend) 
    -> ({F} ta) [<=] ({F} tb).

Definition nonIncreasingDuring (F : TContR) (tstart tend : Time) :=
  forall (ta tb: Time), (tstart [<=] ta /\ ta [<=] tb /\ tb [<=] tend) 
    -> ({F} tb) [<=] ({F} ta).
*)

Definition inBetweenR (b a c : IR) 
  := (Min a c [<=] b /\ b [<=] Max a c).

Lemma nonDecreasingIfDerivNonNeg :forall (F F' : TContR)
   (tstart tend : Time) (Hab : tstart[<=]tend),
   isDerivativeOf F' F
   -> nonNegDuring F' tstart tend
   -> ({F} tstart) [<=] ({F} tend).
Proof.
  apply nonDecreasingIfIDerivNonNeg.
Qed.

Lemma nonIncreasingIfDerivNonPos :forall (F F' : TContR)
   (tstart tend : Time) (Hab : tstart[<=]tend),
   isDerivativeOf F' F
   -> nonPosDuring F' tstart tend
   -> ({F} tend) [<=] ({F} tstart).
Proof.
  intros ? ? ? ? ?  Hder Hn.
  unfold nonPosDuring in Hn.
  pose proof (TDerivativeUB3 F F' _ _ Hab [0] Hder) as X.
  rewrite cring_mult_zero_op in X.
  apply shift_leEq_rht.
  apply inv_cancel_leEq. rewrite cg_zero_inv.
  assert ([--] ({F} tstart [-] {F} tend) [=] {F} tend [-] {F} tstart)  as Xx by
    (unfold cg_minus; ring).
  rewrite Xx.
   apply X. intros t Hb.
  apply Hn. simpl in Hb. destruct Hb. split; assumption.
Qed.

Lemma nonNegDuringSplit :forall (F : TContR)
   (tstart t tend : Time) (Hab : tstart[<=]tend)
   (Hb : tstart [<=] t /\ t [<=] tend),
   nonNegDuring F tstart tend
   -> (nonNegDuring F tstart t /\ nonNegDuring F t tend). 
Proof.
  intros ? ? ? ? ? ? Hn.
  split; intros tt Hbb; repnd; 
    apply Hn; split; eauto 2 with CoRN.
Qed.

Lemma nonPosDuringSplit :forall (F : TContR)
   (tstart t tend : Time) (Hab : tstart[<=]tend)
   (Hb : tstart [<=] t /\ t [<=] tend),
   nonPosDuring F tstart tend
   -> (nonPosDuring F tstart t /\ nonPosDuring F t tend). 
Proof.
  intros ? ? ? ? ? ? Hn.
  split; intros tt Hbb; repnd; 
    apply Hn; split; eauto 2 with CoRN.
Qed.

Lemma nonSignChangeMult :forall (F G : TContR)
   (tstart tend : Time) (Hab : tstart[<=]tend),
   noSignChangeDuring F tstart tend
   -> noSignChangeDuring G tstart tend
   -> noSignChangeDuring (F [*] G) tstart tend.
Proof.
  intros ? ? ? ? ? Hf Hg.
  destruct Hf, Hg.
  - left. intros t Hb. simpl. apply mult_resp_nonneg;
    auto.
  - right. intros t Hb. simpl.
    apply inv_cancel_leEq.
    rewrite cg_zero_inv.
    rewrite <- cring_inv_mult_lft.
    apply mult_resp_nonneg;[auto|].
    apply inv_cancel_leEq.
    rewrite cg_zero_inv, cg_inv_inv. auto.
  - right. intros t Hb. simpl.
    apply inv_cancel_leEq.
    rewrite cg_zero_inv.
    rewrite <- cring_inv_mult_rht.
    apply mult_resp_nonneg;[|auto].
    apply inv_cancel_leEq.
    rewrite cg_zero_inv, cg_inv_inv. auto.
  - left. intros t Hb. simpl.
    match goal with
    [ |- _ [<=] ?r] => rewrite <- (cg_inv_inv _ r)
    end.
    rewrite <- cring_inv_mult_rht.
    rewrite <- cring_inv_mult_lft.
    apply mult_resp_nonneg;
    apply inv_cancel_leEq;
    rewrite cg_zero_inv, cg_inv_inv; auto.
Qed.

Lemma nosignChangeInBw :forall (F F' : TContR)
   (tstart tend : Time) (Hab : tstart[<=]tend),
   isDerivativeOf F' F
   -> noSignChangeDuring F' tstart tend
   -> forall (t: Time), (tstart [<=] t /\ t [<=] tend)
      -> inBetweenR ({F} t) ({F} tstart) ({F} tend).
Proof.
  intros ? ? ? ? ?  Hder Hn t Hb.
  destruct Hn as [Hinc | Hdec].
  - unfold inBetweenR.
    rewrite leEq_imp_Min_is_lft;
      [| eapply nonDecreasingIfDerivNonNeg; eauto].
    rewrite leEq_imp_Max_is_rht;
      [| eapply nonDecreasingIfDerivNonNeg; eauto].
    pose proof Hb as Hbbb.
    eapply nonNegDuringSplit in Hb; eauto.
    repnd.
    split; eapply nonDecreasingIfDerivNonNeg; eauto.
  - unfold inBetweenR. rewrite Min_comm, Max_comm.
    rewrite leEq_imp_Min_is_lft;
      [| eapply nonIncreasingIfDerivNonPos; eauto].
    rewrite leEq_imp_Max_is_rht;
      [| eapply nonIncreasingIfDerivNonPos; eauto].
    pose proof Hb as Hbbb.
    eapply nonPosDuringSplit in Hb; eauto.
    repnd.
    split; eapply nonIncreasingIfDerivNonPos; eauto.
Qed.
  Local Opaque Min Max. 
Lemma DerivNonNegIntegral :forall (F : TContR)
   (tstart tend : Time) (Hab : tstart[<=]tend),
   nonNegDuring F tstart tend
   -> [0] [<=] (Cintegral (mkIntBnd Hab) F).
Proof.
  intros ? ? ? ?  Hn.
  rewrite <- CintegralZero with (p:=Hab) at 1.
  apply IntegralMonotone. 
  simpl.
  intros t Hb. destruct Hb as [Hbl Hbr].
  rewrite leEq_imp_Min_is_lft in Hbl; [| assumption].
  rewrite leEq_imp_Max_is_rht in Hbr; [| assumption].
  apply Hn. tauto.
Qed.

(*exact same proof as above*)
Lemma DerivNonPosIntegral :forall (F : TContR)
   (tstart tend : Time) (Hab : tstart[<=]tend),
   nonPosDuring F tstart tend
   -> (Cintegral (mkIntBnd Hab) F) [<=] [0].
Proof.
  intros ? ? ? ?  Hn.
  rewrite <- CintegralZero with (p:=Hab) at 3.
  apply IntegralMonotone. 
  simpl.
  intros t Hb. destruct Hb as [Hbl Hbr].
  rewrite leEq_imp_Min_is_lft in Hbl; [| assumption].
  rewrite leEq_imp_Max_is_rht in Hbr; [| assumption].
  apply Hn. tauto.
Qed.


Lemma nosignChangeInBwInt :forall (F : TContR)
   (tstart tend : Time) (Hab : tstart[<=]tend),
   noSignChangeDuring F tstart tend
   -> forall (t: Time) (pl: tstart [<=] t) (pr:t [<=] tend),
        inBetweenR (Cintegral (mkIntBnd pl) F) 
                   [0] 
                   (Cintegral (mkIntBnd Hab) F).
Proof.
  intros ? ? ? ?  Hn ? ? ?.
  unfold inBetweenR.
  destruct Hn as [Hn | Hn].
  - rewrite leEq_imp_Min_is_lft;
      [| eauto using DerivNonNegIntegral].
    rewrite leEq_imp_Max_is_rht;
      [| eauto using DerivNonNegIntegral].
    rewrite CintegralSplit with (pl:=pl) (pr:=pr).
    eapply nonNegDuringSplit in Hn; eauto. repnd.
    split; [eauto using DerivNonNegIntegral|].
    apply shift_leEq_plus'. rewrite cg_minus_correct.
    eauto using DerivNonNegIntegral.
  - rewrite Min_comm, Max_comm.
    rewrite leEq_imp_Min_is_lft;
      [| eauto using DerivNonPosIntegral].
    rewrite leEq_imp_Max_is_rht;
      [| eauto using DerivNonPosIntegral].
    rewrite CintegralSplit with (pl:=pl) (pr:=pr).
    eapply nonPosDuringSplit in Hn; eauto. repnd.
    split; [|eauto using DerivNonPosIntegral].
    rewrite cag_commutes_unfolded.
    apply shift_plus_leEq.
    rewrite cg_minus_correct.
    eauto using DerivNonPosIntegral.
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

Lemma TContRlt:  forall (p : TContR) x y,
        {p} x [<]{p} y 
        -> x[<=]y
        -> x[<]y.
Proof.
  intros ? ? ? Hpp Hle.
  apply extToPartLt2 in Hpp.
  apply pfstrlt in Hpp; auto.
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

Definition between (b a c eps : IR) 
  := ((Min a (c [-] eps)  [<=] b) /\ (b [<=] Max a (c [+] eps))) .

Require Import Coq.QArith.Qminmax.
Ltac InjQRingSimplify :=
  unfold Q2R, Z2R; autorewrite with QSimpl;
let H99 := fresh "HSimplInjQ" in
let H98 := fresh "HSimplInjQ" in
match goal with
[|- context [inj_Q _ ?q]] => pose proof (Qeq_refl q) as H99;
                            ring_simplify in H99;
                            match type of H99 with
                            | (?qn == _)%Q => 
                             assert (q == qn)%Q as H98 by ring;
                             rewrite H98; clear H99; clear H98
                            end
end.


(* Qbetween does not work. [a] needs to be an [IR] 
    even when changesTo is used for [motorSpec].
    With a little more effort, similar lemmas were proven for
    between. So [qbetween] should not be needed at all
 *)
Definition qbetween (b : IR) (a c  : Q) (eps: QTime) 
  := ((Q2R(Qmin a (c - eps))  [<=] b) /\ (b [<=] Qmax a (c + QT2Q eps))) .

Require Export Coq.Unicode.Utf8.
Lemma qbetweenRAbs : ∀ (b : ℝ) (a c : Q) (eps : QTime),
  qbetween b a c eps
  -> AbsIR (b[-]c) [<=] ((Qabs (a-c)) +eps)%Q.
Proof.
  intros ? ? ? ? Hb.
  unfold qbetween in Hb.
  repnd.
  apply AbsSmall_imp_AbsIR.
  unfold AbsSmall.
    Local Opaque Qabs.
  split.
  - ring_simplify.
    apply shift_leEq_minus'.
    eapply leEq_transitive;[|apply Hbl].
    clear Hbl Hbr.
    unfold Q2R. autorewrite with QSimpl.
    apply inj_Q_leEq.
    destruct eps as [eps epsp]. simpl.
    apply QTimeD in epsp.
    apply Q.min_glb;
    apply Qabs_case; intros;  lra.
  - apply shift_minus_leEq.
    eapply leEq_transitive;[apply Hbr|].
    clear Hbl Hbr.
    unfold Q2R. autorewrite with QSimpl.
    apply inj_Q_leEq.
    destruct eps as [eps epsp]. simpl.
    apply QTimeD in epsp.
    apply Q.max_lub;
    apply Qabs_case; intros;  lra.
Qed.

Definition changesTo (f : TContR)
  (atTime uptoTime : QTime)
  (toValue : ℝ)
  (reactionTime eps : Q) :=
(exists  (qt : QTime), 
  atTime <= qt <= (atTime + reactionTime)
  /\ ((forall t : QTime, 
          (qt <= t <= uptoTime -> AbsIR ({f} t [-] toValue) [<=] eps)))
  /\ (forall t : QTime, (atTime <= t <= qt)  
          -> (between ({f} t) ({f} atTime) toValue eps)))%Q.
(** using [eps] here with [between] is great. it means
  that receiving a request to set velocity to the
  current value is a no-op *)

Instance TContR_properR (f : TContR) :
  Proper ((fun (x y : Time) => @st_eq IR x y) ==>  (@st_eq IR))  (fun (q : Time) => {f} q).
Proof.
  intros ? ? Heq. apply  csf_fun_wd. unfold Basics.flip in Heq.
  destruct x,y. simpl. simpl in Heq.  exact Heq.
Qed.


Instance TContR_proper (f : TContR) :
  Proper ((fun (x y : QTime) => Qeq x y) ==> (@st_eq IR)) (fun (q : QTime) => {f} q).
Proof.
  intros ? ? Heq. apply TContR_properR. simpl. destruct x. destruct y. simpl.
  simpl in Heq. apply inj_Q_wd.
    exact Heq.
Qed.

Hint Rewrite Max_id  Min_id cring_mult_zero_op : CoRN.

Lemma TDerivativeEqAux :forall (F F' : TContR)
   (ta tb : Time) (Hab : ta [<] tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:Time), ta [<=] t /\ t [<=] tb -> ({F'} t) [=] c)
   -> ({F} tb[-] {F} ta)[=]c[*](tb[-]ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  apply leEq_imp_eq;
    [apply (@TDerivativeUB _ _ _ _ Hab c Hder) | apply (@TDerivativeLB _ _ _ _ Hab c Hder)];
    intros ? Hbw Hd; unfold compact in Hbw; pose proof (conj (fst Hbw) (snd Hbw)) as Hbp;
    rewrite <- extToPart2; rewrite (Hub (mkRIntvl (closel [0]) x Hd) Hbp);
    apply leEq_reflexive.
Qed.

(** use a double negation trick to weaken the assumptuin [ta [<] tb] to [ta [<=] tb]*)
Lemma TDerivativeEq :forall (F F' : TContR)
   (ta tb : Time) (Hab : ta [<=] tb) (c : ℝ),
   isDerivativeOf F' F
   -> (forall (t:Time), ta [<=] t /\ t [<=] tb -> ({F'} t) [=] c)
   -> ({F} tb[-] {F} ta)[=]c[*](tb[-]ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  apply not_ap_imp_eq.
  apply leEq_less_or_equal in Hab. rename Hab into Hd.
  intro Hc.
  apply Hd.
  clear Hd. intro Hd.
  apply ap_tight in Hc;[contradiction|]. clear H Hc.
  destruct Hd as [Hd | Hd];
    [eapply TDerivativeEqAux; eauto|].
  rewrite Hd.
  rewrite (@TContR_properR  F ta tb Hd).
  unfold cg_minus. ring.
Qed.


(** use a double negation trick to weaken the assumptuin [ta [<] tb] to [ta [<=] tb]*)
Lemma TDerivativeEq0 :forall (F F' : TContR)
   (ta tb : Time) (Hab : ta [<=] tb),
   isDerivativeOf F' F
   -> (forall (t:Time), ta [<=] t /\ t [<=] tb -> ({F'} t) [=] [0])
   -> {F} tb [=] {F} ta.
Proof.
  intros ? ?  ? ? ? Hder Hub.
  eapply TDerivativeEq in Hub; eauto.
  rewrite cring_mult_zero_op in Hub.
  remember ({F} ta) as fta.
  remember ({F} tb) as ftb.
  assert (fta[=]fta [+] [0]) as H by ring.
  rewrite H.
  rewrite <- Hub. unfold cg_minus. ring.
Qed.

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

Require Import IRMisc.LegacyIRRing.

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



Lemma  qtimePosIR : ∀ y,  [0][<=]QT2R y.
  intros. rewrite <- inj_Q_Zero.
  apply inj_Q_leEq.
  apply qtimePos.
Qed.
Hint Resolve qtimePosIR : ROSCOQ.

Lemma changesToDerivSameDeriv :  ∀ (F': TContR)
  (atTime uptoTime : QTime) (val : IR) (eps : QTime)
  (reactionTime : Q),
  atTime <= uptoTime
  → changesTo F' atTime uptoTime val reactionTime eps
  → {F'} atTime [=] val
  → ∀ (t : QTime), atTime <= t <= uptoTime 
      → AbsIR({F'} t [-] val) [<=] QT2Q eps.
Proof.
  intros ? ? ? ? ? ? Hle Hc Hf0.
  unfold changesTo in Hc.
  destruct Hc as [qtrans  Hm]. repnd.
  pose proof (Q_dec atTime uptoTime) as Htric.
  intros ? Hbw. repnd.
  destruct Htric as [Htric | Htric].
  Focus 2.
    assert (t==atTime) as Heq by lra.
    apply TContR_proper with (f:=F') in Heq.
    rewrite Heq, Hf0.
    rewrite cg_minus_correct, AbsIRz_isz.
    fold (QT2R eps).
    eauto with ROSCOQ; fail.

  destruct Htric as [Htric | Htric] ;[|lra].
  assert (proper (clcr (QT2Q atTime) (QT2Q uptoTime))) as pJ by UnfoldLRA.
  unfold between in Hmrr.
  setoid_rewrite Hf0 in Hmrr.
  setoid_rewrite Min_comm in Hmrr.
  pose proof (leEq_imp_Min_is_lft (val[-]QT2R eps) val) as Hm.
  DestImp Hm;[|eauto 3 with CoRN ROSCOQ; fail].
  setoid_rewrite Hm in Hmrr. clear Hm.
  pose proof (leEq_imp_Max_is_rht val (val[+]QT2R eps)) as Hm.
  DestImp Hm;[|eauto 3 with CoRN ROSCOQ; fail].
  setoid_rewrite Hm in Hmrr.
  unfold QT2R in Hmrr.
  rename t into qt.
  pose proof (Qlt_le_dec qt qtrans) as Hdec.
  Dor Hdec;[clear Hmrl | clear Hmrr].
- apply Qlt_le_weak in Hdec.
  specialize (Hmrr qt (conj Hbwl Hdec)). repnd.
  apply AbsSmall_imp_AbsIR.
  unfold AbsSmall. repnd.
  split; [apply shift_leEq_minus| apply shift_minus_leEq];
    eapply leEq_transitive; eauto;
    apply eqImpliesLeEq; unfold cg_minus; ring.
- assert (qt <= uptoTime) as Hup by lra.
  specialize (Hmrl qt (conj Hdec Hup)).
  assumption.
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
  intros ? ? ? ? Hle Hc Hf0 ? Hb.
  assert (0= QT2Q (mkQTime 0 I)) as Heq by reflexivity.
  rewrite Heq in Hc.
  eapply changesToDerivSameDeriv in Hc; eauto.
  Local Opaque Q2R AbsIR.
  simpl in Hc.
  setoid_rewrite minusQ2R0 in Hc.
  rewrite Q2R0IsR0 in Hc.
  rewrite Q2R0IsR0.
  apply AbsIRLe0; assumption.
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


Local Transparent Q2R.
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

  Hint Rewrite  inj_Q_One : InjQDown.
  Hint Rewrite  inj_Q_inv : InjQDown.
  Hint Rewrite  inj_Q_plus : InjQDown.
  Hint Rewrite  inj_Q_minus : InjQDown.
  Hint Rewrite  inj_Q_inv : InjQDown.
  Hint Rewrite  inj_Q_mult : InjQDown.

Lemma Qminus0 : ∀ x : Q, x - x == 0.
Proof. intros. ring.
Qed.

Hint Rewrite Qminus0 : CoRN.
Lemma changesToDerivSameEpsInteg :  ∀ (F' F: TContR)
  (atTime uptoTime : QTime) (val : IR)
  (reactionTime : Q)  (eps : QTime),
  atTime <= uptoTime
  → changesTo F' atTime uptoTime val reactionTime eps
  → {F'} atTime [=] val 
  → isDerivativeOf F' F
  → ∀ (t : QTime), atTime <= t <= uptoTime 
      → AbsIR({F} t[-] {F} atTime [-] val[*](t-atTime))
         [<=] (QT2R eps) [*] (t - atTime).
Proof.
  intros ? ? ? ? ? ? ?   Hle Hc Hf0 Hd.
  pose proof (Q_dec atTime uptoTime) as Htric.
  intros ? Hbw. repnd.
  destruct Htric as [Htric | Htric].
    Focus 2.  
      assert (t==atTime) as Heq by lra.
      rewrite Heq.
      apply TContR_proper with (f:=F) in Heq.
      rewrite Heq.
      autorewrite with CoRN.
      unfold Q2R. rewrite inj_Q_Zero.
      autorewrite with CoRN. eauto 1 with CoRN; fail.

  destruct Htric as [Htric | Htric] ;[|lra]. 
  apply TDerivativeAbsQ with (F':=F');try tauto.
  intros tl Hb.
  eapply changesToDerivSameDeriv in Hc; eauto.
  repnd. lra.
Qed.

Lemma changesToDerivSameEpsIntegWeaken :  ∀ (F' F: TContR)
  (atTime uptoTime : QTime) (val : IR)
  (reactionTime : Q)  (eps : QTime),
  atTime <= uptoTime
  → changesTo F' atTime uptoTime val reactionTime eps
  → {F'} atTime [=] val 
  → isDerivativeOf F' F
  → ∀ (t : QTime), atTime <= t <= uptoTime 
      → AbsIR({F} t[-] {F} atTime [-] val[*](t-atTime))
         [<=] (QT2R eps) [*] (uptoTime  - atTime).
Proof.
  intros ? ? ? ? ? ? ?   Hle Hc Hf0 Hd t Hb.
  eapply changesToDerivSameEpsInteg in Hc; eauto.
  eapply leEq_transitive;[apply Hc|].
  apply mult_resp_leEq_lft;[|eauto 2 with ROSCOQ; fail].
  repnd. apply inj_Q_leEq. simpl.
  lra.
Qed.

Lemma changesToDerivSameEpsIntegEnd :  ∀ (F' F: TContR)
  (atTime uptoTime : QTime) (val : IR)
  (reactionTime : Q)  (eps : QTime),
  atTime <= uptoTime
  → changesTo F' atTime uptoTime val reactionTime eps
  → {F'} atTime [=] val 
  → isDerivativeOf F' F
  →  AbsIR({F} uptoTime[-] {F} atTime [-] val[*](uptoTime-atTime))
         [<=] (QT2R eps) [*] (uptoTime - atTime).
Proof.
  intros ? ? ? ? ? ? ?   Hle Hc Hf0 Hd.
  eapply changesToDerivSameEpsInteg; eauto.
  repnd. lra.
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


Lemma TwoOnePlusOne : 2 [=] [1][+][1].
Proof.
  assert (2==1+1) as H by reflexivity.
  rewrite H. unfold Q2R. autorewrite with QSimpl.
  reflexivity.
Qed.

Lemma Min_plus : forall (a b c : IR),
Min (a[+]c) (b[+]c) [=] Min a b [+] c.
Proof.
 intros.
 apply equiv_imp_eq_min; intros.
   apply shift_leEq_plus.
   apply leEq_Min; apply shift_minus_leEq; auto.
  apply leEq_transitive with (Min a b [+]c); auto.
  apply plus_resp_leEq.
  apply Min_leEq_lft.
 apply leEq_transitive with (Min a b [+]c); auto.
 apply plus_resp_leEq.
 apply Min_leEq_rht.
Qed.



Lemma betweenRAbs : ∀ (b a c eps : IR),
  [0] [<=] eps 
  -> between b a c eps
  -> AbsIR (b[-]c) [<=] (AbsIR (a[-]c)) [+]eps.
Proof.
  intros ? ? ? ? Hle Hb.
  unfold between in Hb.
  repnd.
  apply AbsSmall_imp_AbsIR.
  unfold AbsSmall.
  split;[clear Hbr| clear Hbl].
  - ring_simplify.
    apply shift_leEq_minus'.
    eapply leEq_transitive;[|apply Hbl].
    clear Hbl.
    assert (c[+]([--](AbsIR (a[-]c))[-]eps)
            [=] (c[-]AbsIR (a[-]c))[-]eps) as Heq by
            (unfold cg_minus; ring).
    rewrite Heq. clear Heq. apply leEq_Min.
    + apply minusSwapLe. eapply leEq_transitive;[| apply Hle].
      assert (c[-]AbsIR (a[-]c)[-]a [=] (c[-]a[-]AbsIR (a[-]c)))
        as Heq by (unfold cg_minus; ring).
      rewrite Heq.
      apply shift_minus_leEq. ring_simplify.
      rewrite AbsIR_minus.
      apply leEq_AbsIR.
    + apply minus_resp_leEq.
      apply shift_minus_leEq.
      apply addNNegLeEq.
      apply AbsIR_nonneg.
  - apply shift_minus_leEq.
    eapply leEq_transitive;[apply Hbr|].
    clear Hbr.
    assert (AbsIR (a[-]c)[+]eps[+]c
            [=] (c[+]AbsIR (a[-]c))[+]eps) as Heq by
            (unfold cg_minus; ring).
    rewrite Heq. clear Heq. apply Max_leEq.
    + assert (a[+][0][<=]c[+]AbsIR (a[-]c)[+]eps) as Hx;
        [| ring_simplify in Hx; assumption].
      apply plus_resp_leEq_both; [|assumption].
      apply shift_leEq_plus'.
      apply leEq_AbsIR.
    + apply plus_resp_leEq.
      apply addNNegLeEq.
      apply AbsIR_nonneg.
Qed.

Lemma betweenLAbs : ∀ (b a c eps : IR),
  [0] [<=] eps 
  -> between b a c eps
  -> AbsIR (b[-]a) [<=] AbsIR (a[-]c) [+]eps.
Proof.
  intros ? ? ? ? Hle Hb.
  unfold between in Hb.
  repnd.
  apply AbsSmall_imp_AbsIR.
  unfold AbsSmall.
  split;[clear Hbr| clear Hbl].
  - ring_simplify.
    apply shift_leEq_minus'.
    eapply leEq_transitive;[|apply Hbl].
    clear Hbl.
    assert (a[+]([--](AbsIR (a[-]c))[-]eps)
            [=] (a[-]AbsIR (a[-]c))[-]eps) as Heq by
            (unfold cg_minus; ring).
    rewrite Heq. clear Heq. apply leEq_Min.
    + apply minusSwapLe. eapply leEq_transitive;[| apply Hle].
      assert (a[-]AbsIR (a[-]c)[-]a [=] (a[-]a[-]AbsIR (a[-]c)))
        as Heq by (unfold cg_minus; ring).
      rewrite Heq.
      apply shift_minus_leEq. ring_simplify.
      rewrite cg_minus_correct.
      apply AbsIR_nonneg.
    + apply minus_resp_leEq.
      apply shift_minus_leEq.
      apply shift_leEq_plus'.
      apply leEq_AbsIR.
  - apply shift_minus_leEq.
    eapply leEq_transitive;[apply Hbr|].
    clear Hbr.
    assert (AbsIR (a[-]c)[+]eps[+]a
            [=] (a[+]AbsIR (a[-]c))[+]eps) as Heq by
            (unfold cg_minus; ring).
    rewrite Heq. clear Heq. apply Max_leEq.
    + assert (a[+][0][<=]a[+]AbsIR (a[-]c)[+]eps) as Hx;
        [| ring_simplify in Hx; assumption].
      apply plus_resp_leEq_both; [|assumption].
      apply shift_leEq_plus'.
      rewrite cg_minus_correct.
      apply AbsIR_nonneg.
    + apply plus_resp_leEq.
      apply shift_leEq_plus'.
      rewrite AbsIR_minus.
      apply leEq_AbsIR.
Qed.


Local Opaque Q2R.

Lemma mult_resp_AbsSmallR:  ∀ (x y e : IR),
  [0][<=]y 
  → AbsSmall e x 
  → AbsSmall (e[*]y) (x[*]y).
Proof.
  intros ? ? ? Hle Hs.
  rewrite mult_commutes.
  setoid_rewrite mult_commutes at 2.
  apply mult_resp_AbsSmall;
  assumption.
Qed.


Lemma mult_resp_AbsSmallRQt:  ∀ (x e : IR) (y : QTime),
 AbsSmall e x 
  → AbsSmall (e[*] QT2R y) (x[*] QT2R y).
Proof.
  intros ? ? ? Hle. apply mult_resp_AbsSmallR; trivial;[].
  apply qtimePosIR.
Qed.
  Hint Rewrite <-  inj_Q_mult : QSimpl.



Lemma changesToDerivInteg :  ∀ (F' F: TContR)
  (atTime uptoTime reacTime : QTime) (oldVal newVal : IR)
  ( eps : QTime),
  atTime < uptoTime
  → changesTo F' atTime uptoTime newVal reacTime eps
  → {F'} atTime [=] oldVal 
  → isDerivativeOf F' F
  → let eps1 := (AbsIR ({F'} atTime[-]newVal)) in
    exists qtrans : QTime,  atTime <= qtrans <= atTime + reacTime
      ∧  AbsIR({F} uptoTime[-]{F} atTime[-]newVal[*](uptoTime - atTime))
          [<=] eps1[*](qtrans - atTime) [+] (QT2Q eps)[*](uptoTime - atTime).
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
  pose proof (λ t p, (betweenRAbs _ _ _ _ (qtimePosIR eps) (Hmrr t p)))
     as Hqt. clear Hmrr.
  fold eps1 in Hqt.
  destruct (Qlt_le_dec uptoTime qtrans) as [Ht | Ht].
- pattern qtrans in Hqt.
  match type of Hqt with
   ?f _  => assert (f uptoTime) as Hqtt by
      (intros; apply Hqt;split; lra)
  end.
  clear Hqt. simpl in Hqtt. rename Hqtt into Hqt.
  apply TDerivativeAbsQ with (F:=F) in Hqt;[|lra|auto].
  eapply leEq_transitive;[apply Hqt|].
  revert Ht. clear. intro Ht.
  ring_simplify.
Local Transparent Q2R.
  unfold QT2R, Q2R.
  autorewrite with QSimpl.
  apply plus_resp_leEq.
  apply mult_resp_leEq_lft;
    [|subst eps1;eauto 1 with CoRN].
  apply inj_Q_leEq.
  simpl. lra.
- apply TDerivativeAbsQ with (F:=F) in Hqt;[|auto|auto].
  apply TDerivativeAbsQ with (F:=F) in Hmrl;[|lra|auto].
  pose proof (plus_resp_leEq_both _ _ _ _ _ Hqt Hmrl) as Hp.
  eapply leEq_transitive in Hp;[| apply triangle_IR].
Local Transparent Q2R.
  unfold Q2R. ring_simplify in Hp.
  rewrite <- plus_assoc in Hp.
  unfold QT2R in Hp. autorewrite with QSimpl in Hp.
  assert ((QT2Q eps)[*](qtrans - atTime)[+](QT2Q eps)[*](uptoTime - qtrans)
        == (QT2Q eps)[*](uptoTime - atTime))%Q as Heq by (simpl; ring).
  rewrite Heq in Hp.
  clear Heq.
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
  atTime < uptoTime
  → changesTo F' atTime uptoTime newVal reacTime eps
  → {F'} atTime [=] oldVal 
  → isDerivativeOf F' F
  → let eps1 := (AbsIR ({F'} atTime[-]newVal)) in
     AbsIR({F} uptoTime[-]{F} atTime[-]newVal[*](uptoTime - atTime))
          [<=] (eps1)[*](QT2R reacTime) [+]  eps*(uptoTime - atTime).
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
  pose proof (qtimePos eps).
  subst eps1. autorewrite with QSimpl. apply  AbsIR_nonneg.
- unfold Q2R.
  apply inj_Q_leEq. simpl.
  apply Q.Qmult_le_compat_l;[lra|].
  apply qtimePos.
Qed.

Lemma TDerivativeAbsQ0 :forall (F F' : TContR)
   (ta tb : QTime) (Hab : (ta <= tb)%Q) (eps: ℝ),
   isDerivativeOf F' F
   -> (forall (t:QTime), (ta <= t <= tb)%Q -> AbsIR ({F'} t) [<=] eps)
   -> AbsIR({F} tb[-] {F} ta) [<=] eps [*] (tb - ta)%Q.
Proof.
  intros ? ? ? ? ? ? ? Hub.
  assert (∀ t : QTime, (ta <= t <= tb)%Q → AbsIR ({F'} t [-] [0])[<=]eps)
    as Has by (intros; autorewrite with CoRN; auto).
  clear Hub.
  eapply TDerivativeAbsQ in Has; eauto.
  autorewrite with CoRN in Has.
  assumption.
Qed.


(*
Lemma changesToDeriv0EpsInteg :  ∀ (F' F: TContR)
  (atTime uptoTime reacTime : QTime)
  ( eps : QTime),
  atTime + reacTime < uptoTime
  → changesTo F' atTime uptoTime newVal reacTime eps
  → {F'} atTime [=] oldVal 
  → isDerivativeOf F' F
  → let eps1 := (AbsIR ({F'} atTime[-]newVal)) in
     AbsIR({F} uptoTime[-]{F} atTime[-]newVal[*](uptoTime - atTime))
          [<=] (eps1)[*](QT2R reacTime) [+]  eps*(uptoTime - atTime).
*)
Definition TIntgBnds : Type := IntgBnds (closel [0]).



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


Notation "Z⁺" := positive.

Definition mkIntBndQ {a b : QTime} 
(p : a <= b%Q) : IntgBnds (closel [0]).
  exists (QT2T a, QT2T b). simpl.
  rewrite <- QT2T_Q2R, <- QT2T_Q2R.
  apply inj_Q_leEq.
  exact p.
Defined.


Lemma TBarrowQ : ∀ (F F': TContR)
         (der : isIDerivativeOf F' F) (a b : QTime)
          (p: a <= b%Q),
       {F} b [-] {F} a [=] Cintegral (mkIntBndQ  p) F'.
Proof.
  intros. symmetry.
  apply TBarrow. assumption.
Qed.

(** for continuous functions, equality at rational points suffices for all other points*)
Lemma EqRationalCont : ∀ (F G: TContR) (a b : QTime) (p: a <= b%Q), 
(forall t:QTime, (a<=t<=b)%Q -> {F} t [=] {G} t)
-> IContREqInIntvl (mkIntBndQ p) F G.
Proof.
  intros ? ? ? ? ? Hq.
  intros z Hb. unfold inBounds in Hb. simpl in Hb.
  apply cg_inv_unique_2. rewrite <- IContRMinusAp.
  rewrite <- QT2T_Q2R in Hb. rewrite <- QT2T_Q2R in Hb.
  apply TContRR2QCompactIntEq2 with (ta:=a) (tb:=b); try assumption;[].
  intros ? Hbb.
  apply Hq in Hbb.
  autorewrite with IContRApDown.
  rewrite Hbb. unfold cg_minus. ring.
Qed.

(* TODO : it should suffice to make Time be QTime in the last hypothesis *)
Lemma TBarrowScale : ∀ (F F' G': TContR)
         (der : isIDerivativeOf F' F) (ib : IntgBnds _) (c:IR),
       (forall t:Time, ((intgBndL ib) [<=]t /\ t[<=](intgBndR ib)) -> {F'} t [=] c [*] ({G'} t))
       -> {F} (intgBndR ib) [-] {F} (intgBndL ib) [=] c [*] (Cintegral ib G').
Proof.
  intros ? ? ? ? ?  ? Hc.
  setoid_rewrite <- (@TBarrowEta _ _ _ _ der ib).
  rewrite <- CIntegral_scale.
  apply Cintegral_wd2. 
  unfold IContREqInIntvl.
  intros ? Hb.
  autorewrite with IContRApDown.
  apply Hc. exact Hb.
Qed.

Lemma TBarrowQScale : ∀ (F F' G': TContR)
         (der : isIDerivativeOf F' F) (a b : QTime) (c:IR)
          (p: a <= b%Q),
       (forall t:QTime, (a<=t<=b)%Q -> {F'} t [=] c [*] ({G'} t))
       -> {F} b [-] {F} a [=] c [*] (Cintegral (mkIntBndQ  p) G').
Proof.
  intros ? ? ? ? ? ? ? ? Hc.
  rewrite (TBarrowQ _ _ der a b p).
  rewrite <- CIntegral_scale.
  apply Cintegral_wd2. 
  unfold IContREqInIntvl.
  apply EqRationalCont.
  intros ? Hb.
  autorewrite with IContRApDown.
  apply Hc. assumption.
Qed.