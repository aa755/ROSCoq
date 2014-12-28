Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.


Require Export CoRN.ftc.MoreIntervals.


  
(* Definition N2Q (n: nat) : Q := n. *)

Notation "x × y" := (prod x y) (at level 80, right associativity) : type_scope.

(* Coercion N2Q : nat >-> Q. *)

Definition ninv (n: nat) : Q :=
  Qinv (n).

Definition R := IR.

Require Export Coq.ZArith.ZArith.

Require Export CoRNMisc.


Definition N2R  (n: nat) : IR := (inj_Q IR  (inject_Z n)).


(** Time is modeled as a real number. One is allowed to make non-deterministic
   decisions on time *)



Notation "a < b < c" := (Qlt a  b /\  Qlt b  c) : Q_scope .


Notation "A & B" := (prod A B)  (at level 80, right associativity).
(*
Notation "a [<] b [<] c" := (a [<] b &  b [<] c) : R_scope.
Notation "a [<=] b [<=] c" := (a [<=] b &  b [<=] c) : R_scope.
*)


Record RInInterval (intvl : interval)  := {
  realV :> R;
  realVPos : iprop intvl realV
}.

Definition RNonNeg := RInInterval (closel [0]).
Definition RPos := RInInterval (openl [0]).

Definition restrictToInterval {A} (f : R -> A) 
    (intvl : interval) : (RInInterval intvl) -> A :=
    fun r => f r.


Definition Time := RNonNeg.
Open Scope Q_scope.


Definition Qpos : Type := {q : Q | 0 < q}.

Definition Qp2Q (t : Qpos) : Q := (proj1_sig t).
Coercion Qp2Q : Qpos >-> Q.

(*
Definition Time : Type := {q : Q | 0 <= q}.
Definition T2Q (t : Time) : Q := (proj1_sig t).
Coercion T2Q : Time >-> Q.
*)

(*
Lemma restrictTill {A} (f : Time -> A) 
    (right : Time) : (RInInterval (clcr [0] right)) -> A.
  intro rint.
  destruct rint.
  apply f. exists realV0.
  unfold iprop.
  unfold iprop in realVPos0.
  destruct realVPos0.
  trivial.
Defined.

Lemma fastFwd {A} (f : Time -> A) 
    (duration : Time) : Time  -> A.
  intro rint.
  destruct rint.
  apply f. exists (realV0 [+] duration).
  destruct duration. simpl.
  unfold iprop.
  unfold iprop in realVPos0.
  unfold iprop in realVPos1.
  eauto with *.
Defined.
*)

Definition tdiff (t tl : Time) : Time.
(*  exists (Qabs (tl - t)).
  apply Qabs_nonneg. *)

  exists (AbsIR (tl [-] t)).
  unfold iprop. apply AbsIR_nonneg.
Defined.

Hint Resolve plus_resp_nonneg : CoRN. 
 Definition tadd (t tl : Time) : Time.
   exists (tl [+] t).
   unfold iprop. destruct t. destruct tl.
   simpl. unfold iprop in realVPos0.
   unfold iprop in realVPos1.
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


Definition QNNeg : Type := {q : Q | (if Qlt_le_dec q 0 then False else True) : Prop}.
Definition QTime := QNNeg.

(** if [q] is a closed non-negative rational, then p:=I is guaranteed to work *)
Definition mkQTime (q:Q) (p: (if Qlt_le_dec q 0 then False else True)) : QTime
:= exist _ q p.



Definition QT2Q (t : QTime) : Q := let (x, _) := t in x.

Coercion QT2Q : QTime >-> Q.

Definition QT2T (q: QTime) : Time.
  destruct q as [q qp].
  exists (Q2R q). simpl.
  unfold Q2R.
  rewrite <- inj_Q_Zero.
  apply inj_Q_leEq. simpl.
  destruct (Qlt_le_dec q 0); auto.
  contradiction.
Defined.

Definition QT2R (q: QTime) : R.
  destruct q.
  exact (x).
Defined.

Coercion N2T : nat >-> Time.
  (* Q.Qle_nat *)

Coercion QT2T : QTime >-> Time.

(*
Definition N2QTime (n: nat) : QTime.
  exists (n). destruct n; simpl; auto.
Defined.
Coercion N2QTime : nat >-> QTime.
*)


(*
Definition fastFwdAndRestrict {A}
    (f : Time -> A) (tstart tend : Time) :
      (RInInterval (clcr [0] (tdiff tend tstart))) -> A :=
restrictTill (fastFwd f tstart) (tdiff tend tstart).
*)

Definition equalUpto {Value : Type} (t: Time) (f1 f2 : Time -> Value) :=
  forall  (ti: Time), (ti [<=] t) -> f1 ti = f2 ti.

Set Implicit Arguments.

Definition ConjL (lp : list Prop) : Prop 
  := (fold_left (fun A B => A/\B) lp True).
 

Inductive Cast (T: Type) : Prop :=
cast : T -> Cast T.


Require Import String.


Definition InjectiveFun {A B} (f : A -> B) :=
  forall (a1 a2: A), f a1 = f a2 -> a1 = a2.

Class UniqueNames (T : Type) :=
{
    tname : T -> string;
    tnameInj : InjectiveFun tname
}.

Class DecEq (T : Type) :=
{
    eqdec : forall (a b :T), {a=b} + {a<>b}
}.



Definition boolToProp (b : bool) : Prop :=
match b with
| true => True
| false => False
end.

Open Scope R_scope.

Definition enqueueAll {A : Type} (lel : list A) (oldQueue : list A) : list A :=
     lel ++ oldQueue.

Definition enqueue {A : Type} (el : A) (oldQueue : list A) : list A :=
     enqueueAll (el::nil)  oldQueue.

Definition dequeue {A : Type} (l: list A) : option A * list A :=
match rev l with
| nil => (None, nil)
| last :: rest => (Some last, rev rest)
end.

Lemma dequeueIn : forall {A : Type} (lq: list A),
  let (el,_) := dequeue lq in
  match el with
  | Some ld => In ld lq
  | None => True
  end.
Proof.
  intros. unfold dequeue.
  remember (rev lq) as lqr.
  destruct lqr as [| lh ltl];[tauto|].
  rewrite in_rev.
  rewrite <- Heqlqr.
  auto.
Qed.


Require Export CoRN.reals.Q_in_CReals.

Definition Z2R  (n: Z) : R := (inj_Q IR  (inject_Z n)).

Definition overApproximate (t: R) : { z:  Z | t  [<] Z2R z}.
  remember (start_of_sequence _ t).
  clear Heqs. destruct s as [qf Hp]. destruct Hp as [qc Hpp].
  exists (Qround.Qceiling qc).
  unfold Z2R. pose proof (Qround.Qle_ceiling qc) as Hq.
  apply (inj_Q_leEq IR) in Hq.
  eauto  using less_leEq_trans.
Defined.

(*
Definition overApproximateN (t: R) : { n: nat | t  [<] N2R n}.
destruct (overApproximate t) as [zf  Hp].
exists (Z.to_N zf).
*)


Definition RTime :=Time.


Lemma N2R_add_commute : forall (n1 n2 : nat),
  N2R n1 [+] N2R n2 = N2R (n1 + n2).
Abort.


(** Much of the work in defining devices is to decide what the inputs
    and outputs are and what property they specify. Each device is defined
    in it's own file *)

Close Scope R_scope.


(** A [TimeFun] is a partial function from reals to reals,
   such that its domain includes the non-negative reals.
   From this, one can extract a member of [Time -> R]
   representing how the physical quantity changed over time.
  [PartIR] ensures functionality, unlike  [Time -> R] *)
Record TimeFun := 
 { f :> PartIR ;
  continTF :  Continuous (closel [0]) f
}.

Definition definedOnNonNeg (tf: TimeFun) : included (closel [0]) (pfdom _ tf)
  := (fst (continTF tf)).

Definition getF  (f : TimeFun)  (t :Time ) : R :=
f t ((definedOnNonNeg f) _ (realVPos _ t)).

Notation "{ f }" := (getF f).


Definition isDerivativeOf (F' F : TimeFun) : CProp :=
Derivative (closel [0]) I F F'.

Lemma timeIncluded : forall (ta tb : Time),
  included (clcr ta tb) (closel [0]).
Proof.
 destruct ta as [ra pa].
 destruct tb as [rb pb].
 simpl. simpl in pa. simpl in pb.
 unfold included. intros ? Hlft.
 simpl in Hlft.
 destruct Hlft. simpl.
 eauto using leEq_transitive.
Qed.

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

Definition mkQTimeInj  (t : Q) (tl: QTime) (p: Q2R tl [<=] Q2R t) : QTime.
  eapply mkQTime1.
  apply leEq_inj_Q in p.
  apply p.
Defined.


Lemma timeIncludedQ : forall (ta tb : QTime),
  included (clcr ta tb) (closel [0]).
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

Lemma TDerivativeUB :forall {F F' : TimeFun}
   (ta tb : Time) (Hab : ta[<]tb) (c : R),
   isDerivativeOf F' F
   -> UBoundInCompInt Hab F' c
   -> ((getF F) tb[-] (getF F) ta)[<=]c[*](tb[-]ta).
Proof.
 intros ? ? ? ? ? ? Hisd Hub.
 unfold getF.
 apply (AntiderivativeUB2 F F' ta tb Hab); auto.
 unfold isDerivativeOf in Hisd.
 apply Included_imp_Derivative with 
   (I:=closel [0]) (pI := I); trivial;[].
 apply timeIncluded.
Qed.

Lemma TDerivativeLB :forall {F F' : TimeFun}
   (ta tb : Time) (Hab : ta[<]tb) (c : R),
   isDerivativeOf F' F
   -> LBoundInCompInt Hab F' c
   -> c[*](tb[-]ta) [<=] ((getF F) tb[-] (getF F) ta).
Proof.
 intros ? ? ? ? ? ? Hisd Hub.
 unfold getF.
 apply (AntiderivativeLB2 F F' ta tb Hab); auto.
 unfold isDerivativeOf in Hisd.
 apply Included_imp_Derivative with 
   (I:=closel [0]) (pI := I); trivial;[].
 apply timeIncluded.
Qed.

Definition toTime (t : Time) (r : R) (p :t[<=]r) : Time.
Proof.
  exists r.
  destruct t as [rt  pt].
  simpl in pt.
  simpl.
  eauto using leEq_transitive.
Defined.


Lemma TDerivativeUB2 :forall (F F' : TimeFun)
   (ta tb : Time) (Hab : ta[<]tb) (c : R),
   isDerivativeOf F' F
   -> (forall (t:Time), (clcr ta tb) t -> ({F'} t) [<=] c)
   -> ({F} tb[-] {F} ta)[<=]c[*](tb[-]ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  eapply TDerivativeUB with (Hab0 := Hab); eauto;[].
  unfold UBoundInCompInt.
  intros r Hc ?. unfold compact in Hc.
  unfold getF in Hub.
  destruct Hc as [Hca Hcb].
  specialize (Hub (toTime _ _ Hca)).
  unfold toTime in Hub.
  destruct ta as [ra pa].
  simpl in Hub.
  pose proof (pfwdef _ F' r r Hx
               (definedOnNonNeg F' r (leEq_transitive IR [0] ra r pa Hca))
                (eq_reflexive _ _) ) 
             as Hrwa.  
  rewrite Hrwa.
  clear Hrwa.
  apply Hub.
  split; auto.
Qed.

Lemma TDerivativeLB2 :forall (F F' : TimeFun)
   (ta tb : Time) (Hab : ta[<]tb) (c : R),
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
  unfold toTime in Hub.
  destruct ta as [ra pa].
  simpl in Hub.
  pose proof (pfwdef _ F' r r Hx
               (definedOnNonNeg F' r (leEq_transitive IR [0] ra r pa Hca))
                (eq_reflexive _ _) ) 
             as Hrwa.  
  rewrite Hrwa.
  clear Hrwa.
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


Definition nbdAround ( radius center : R) :=
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

  (*
    apply Q.Qplus_lt_r with (z:= (-qb))  in Hsendlrrr.
    (* ring_simplify in Hsendlrrr. *)

    rewrite Qplus_assoc in Hsendlrrr.
    rewrite <- Qplus_comm in Hsendlrrr.
    fold (Qminus qa qb) in Hsendlrrr.
    rewrite <- (Qplus_comm qb (-qb)) in Hsendlrrr.
    rewrite Qplus_opp_r in Hsendlrrr.
    rewrite Qplus_0_l in Hsendlrrr.
    trivial. 
*)
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

Lemma RemoveOrFalse : forall A , A \/ False <-> A.
Proof.
  tauto.
Qed.


Lemma length1In : forall {A} (l : list A) (a: A),
  In a l 
  -> List.length l = 1%nat
  -> a::nil = l.
Proof.
  intros ? ? ? Hin Hlen.
  destruct l; simpl in Hlen; inversion Hlen as [ Hll].
  destruct l; inversion Hll.
  simpl in Hin. rewrite  RemoveOrFalse in Hin.
  subst. reflexivity.
Qed.


Ltac TrimAndRHS Hyp :=
let H99 := fresh "H99" in 
destruct Hyp as [Hyp H99]; clear H99.

Ltac TrimAndLHS Hyp :=
let H99 := fresh "H99" in 
destruct Hyp as [H99 Hyp]; clear H99.

Ltac repnd :=
  repeat match goal with
           | [ H : _ /\ _ |- _ ] =>
            let lname := fresh H "l" in 
            let rname := fresh H "r" in 
              destruct H as [lname rname]
         end.
  
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

Ltac dands :=
  repeat match goal with
           | [ |- _ /\ _ ] => split
           | [ |- prod _ _ ] => split
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

Lemma contTfQ : forall (tf : TimeFun) (ta tb : QTime), 
    Continuous  (clcr ta tb) tf.
Proof.
  intros ? ? ?.
  pose proof (continTF tf) as Hc.
  eapply Included_imp_Continuous; eauto.
  apply timeIncludedQ.
Qed.

Lemma TimeFunR2QCompactInt : forall (tf : TimeFun)  (ta tb : QTime) (c : R),
(forall (t:QTime), (ta <= t <= tb) -> ({tf} t) [<=] c)
-> (forall (t:Time), ((clcr ta tb) t) -> ({tf} t) [<=] c).
Proof.
  intros ? ? ? ? Hq ? Hint.
  apply ContFunQRLe with (a:=ta) (b:=tb); trivial;
  [apply contTfQ|].
  intros tq ? pp.
  specialize (Hq (mkQTimeInj _ _ (fst pp))).
  specialize (Hq (Q2RClCr _ _ _ pp)).
  unfold getF in Hq.
  simpl in Hq.
  erewrite pfwdef; eauto using leEq_imp_eq,leEq_reflexive.
Qed.

Lemma TimeFunR2QCompactIntGe : forall (tf : TimeFun)  (ta tb : QTime) (c : R),
(forall (t:QTime), (ta <= t <= tb) -> c [<=] ({tf} t))
-> (forall (t:Time), ((clcr ta tb) t) -> c [<=] ({tf} t)).
Proof.
  intros ? ? ? ? Hq ? Hint.
  apply ContFunQRGe with (a:=ta) (b:=tb); trivial;
  [apply contTfQ|].
  intros tq ? pp.
  specialize (Hq (mkQTimeInj _ _ (fst pp))).
  specialize (Hq (Q2RClCr _ _ _ pp)).
  unfold getF in Hq.
  simpl in Hq.
  erewrite pfwdef; eauto using leEq_imp_eq,leEq_reflexive.
Qed.

Lemma QT2T_Q2R : forall (qt:QTime),
  inj_Q IR (QT2Q qt) = realV _ (QT2T qt).
Proof.
  intros. destruct qt as [q p].
  unfold QT2T, QT2Q, QT2R.
  simpl. reflexivity.
Qed.

Lemma TDerivativeUBQ :forall (F F' : TimeFun)
   (ta tb : QTime) (Hab : ta <= tb) (c : R),
   isDerivativeOf F' F
   -> (forall (t:QTime), ta <= t <= tb -> ({F'} t) [<=] c)
   -> ({F} tb[-] {F} ta)[<=]c[*](tb[-]ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  apply Qle_lteq in Hab.
  destruct Hab as [Hlt| Heq].
- unfold Q2R.
  rewrite QT2T_Q2R.
  rewrite QT2T_Q2R.
  eapply TDerivativeUB2; eauto;
    [ rewrite <- QT2T_Q2R;
      rewrite <- QT2T_Q2R;
      apply inj_Q_less; trivial|].
  rewrite <- QT2T_Q2R.
  rewrite <- QT2T_Q2R.
  apply TimeFunR2QCompactInt.
  trivial.
- symmetry in Heq. apply (inj_Q_wd IR) in Heq.
  unfold Q2R.
  rewrite x_minus_x;
    [rewrite x_minus_x; trivial|];
    [rewrite cring_mult_zero; apply leEq_reflexive|].
  apply pfwdef.  rewrite <- QT2T_Q2R. rewrite <- QT2T_Q2R.
  trivial.
Qed.

Lemma TDerivativeLBQ :forall (F F' : TimeFun)
   (ta tb : QTime) (Hab : ta <= tb) (c : R),
   isDerivativeOf F' F
   -> (forall (t:QTime), ta <= t <= tb -> c [<=] ({F'} t))
   -> c[*](tb[-]ta)[<=]({F} tb[-] {F} ta).
Proof.
  intros ? ? ? ? ? ? Hder Hub.
  apply Qle_lteq in Hab.
  destruct Hab as [Hlt| Heq].
- unfold Q2R.
  rewrite QT2T_Q2R.
  rewrite QT2T_Q2R.
  eapply TDerivativeLB2; eauto;
    [ rewrite <- QT2T_Q2R;
      rewrite <- QT2T_Q2R;
      apply inj_Q_less; trivial|].
  rewrite <- QT2T_Q2R.
  rewrite <- QT2T_Q2R.
  apply TimeFunR2QCompactIntGe.
  trivial.
- symmetry in Heq. apply (inj_Q_wd IR) in Heq.
  unfold Q2R.
  rewrite x_minus_x;
    [rewrite x_minus_x|]; trivial;
    [rewrite cring_mult_zero; apply leEq_reflexive|].
  apply pfwdef.  rewrite <- QT2T_Q2R. rewrite <- QT2T_Q2R.
  trivial.
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
