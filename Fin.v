Require Import Coq.Unicode.Utf8.
Require Export StdlibMisc.

\forall
Local Coercion toBool : sumbool >->bool. 

Require Export Arith.
Require Export Arith.EqNat.
Require Omega.


Definition Fin (n:nat)
  := {m:nat | if lt_dec m n then True else False}.


Lemma sdjflksdjsdlkf2: forall n mm: nat, 
  (if lt_dec (S mm) n then True else False)
  -> (if lt_dec mm n then True else False).
Proof.
  intros. 
  destruct (lt_dec (S mm) n) as [? | nlt]; [| contradiction].
  destruct (lt_dec mm n);trivial.
  omega.
Qed.

Lemma sdjflksdjsdlkf3: forall n mm: nat, 
  (if lt_dec (S mm) (S n) then True else False)
  -> (if lt_dec mm n then True else False).
Proof.
  intros. 
  destruct (lt_dec (S mm) (S n)) as [? | nlt]; [| contradiction].
  destruct (lt_dec mm n);trivial.
  omega.
Qed.

Lemma sdjflksdjsdlkf: forall n mm: nat, 
  (if lt_dec mm n then True else False)
  -> (if lt_dec mm (S n) then True else False).
Proof.
  intros. 
  destruct (lt_dec mm (S n)) as [? | nlt];[exact I |].
  destruct (lt_dec mm n);[| trivial].
  omega.
Qed.

Definition FinCast {n : nat} (m : Fin n) : Fin (S n).
  destruct m as [mm  Hlt].
  exists mm.
  apply sdjflksdjsdlkf. trivial.
Defined.

Coercion FinCast : Fin >-> Fin.

Lemma Fin_eq:
  ∀ (n: nat) (fa fb : Fin n),
    (projT1 fa) = (projT1 fb)
    → fa = fb.
Proof.
  intros ? ? ? Heq.
  destruct fa as [a ap].
  destruct fb as [b bp].
  simpl in Heq. simpl.
  subst.
  apply eq_existsT with (ea := eq_refl).
  remember (lt_dec b n); destruct s; destruct ap, bp; auto.
Qed.

Instance Fin_decidable : ∀ (n:nat),  DecEq (Fin n).
Proof.
  constructor.
  intros.
  destruct (NPeano.Nat.eq_dec (projT1 a) (projT1 b)) as [T|F];[left|right].
  - apply Fin_eq; auto.
  - intro Heq. destruct F. destruct a. destruct b.
    inversion Heq.  subst. simpl. reflexivity.
Defined.

(** never used since there might [A] often depends on [n] *)
Fixpoint toList {A : Type} (n : nat) (la : Fin n -> A) {struct n} : list A.
Abort.


Lemma lessThanLtDec: forall m n,  
  m < n
  -> if lt_dec m n then True else False.
Proof.
  intros ? ? Hlt.
  destruct (lt_dec m n); auto.
Defined.

Definition f0 {A : Type}  (n : Fin 0) : A.
  destruct n as [nn pr]. contradiction.
Defined.

Definition fromList {A : Type} (la : list A): Fin (length la) -> A.
Proof.
  induction la; intro fn; destruct fn as [fnn pr];
    simpl in pr;[contradiction |].
  destruct (lt_dec fnn ((length la))) as [ltl |nltl].
  - apply IHla. exists fnn. apply lessThanLtDec; trivial.
  - exact a. (** outermost element has greatest index *)
Defined.

(*
Definition finFunCast {TA : Type} {n: nat} (fsn : Fin (S n) → TA) 
  (fn : Fin n) : TA := (fsn fn).
*)

Definition N2Fin (n: nat) : Fin (S n).
exists n. unfold lt_dec.
destruct (le_dec (S n) (S n)) as [Hs | Hn];[exact I|].
apply Hn. constructor.
Defined.

Definition Fin2N {n : nat} (fn : Fin n): nat := projT1 fn.

Definition predF {n: nat} (fn : Fin n) : Fin n.
  destruct fn as [nn np].
  destruct nn.
- exists 0. trivial.
- exists nn. apply sdjflksdjsdlkf2. trivial.
Defined.

Definition mkFin (m n: nat) (p: if lt_dec m n then True else False) : Fin n:=
  exist _ m p.


Coercion N2Fin : nat >-> Fin.


Definition firstIndexSat {TA : Type} (pred: TA → bool) {n: nat} 
    (fl: Fin n → TA) : option (Fin n).
induction n;[exact None|].
specialize (IHn fl).
destruct IHn as [sn|];[apply Some;  exact sn; fail|].
destruct (pred (fl n));[apply Some;  exact n; fail | exact None].
Defined.

Generalizable Variable TA.


Definition firstIndexEq `{DecEq TA} {n: nat} 
    (fl: Fin n → TA) (a: TA): option (Fin n) :=
  firstIndexSat (λ p, p =?= a) fl.

Definition firstIndexPi1Eq `{DecEq TA} {B: Type} {n: nat} 
    (fl: Fin n → (TA × B)) (a: TA): option (Fin n) :=
  firstIndexSat (λ p, (fst p) =?= a) fl.

Definition notNone {T : Type} (op : option T) : bool :=
match op with
| Some _ => true
| None => false
end.


Definition fnil {A : Fin 0 -> Type} (fn : Fin 0) : A fn.
destruct fn as [? Hc]. simpl in Hc. contradiction.
Defined.

(*
Definition FinSD {n:nat} (f : Fin (S n)) : (projT1 f = n) + {fp : Fin n | projT1 fp = projT1 f}.
induction n;[]
simpl. 
*)