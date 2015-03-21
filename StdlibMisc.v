Require Import Coq.Lists.List.

Set Implicit Arguments.

Notation "x × y" := (prod x y) (at level 80, right associativity) : type_scope.

Definition ConjL (lp : list Prop) : Prop 
  := (fold_left (fun A B => A/\B) lp True).
 

Inductive Squash (T: Type) : Prop :=
squash : T -> Squash T.



Definition InjectiveFun {A B} (f : A -> B) :=
  forall (a1 a2: A), f a1 = f a2 -> a1 = a2.


(* switch to Require MathClasses.misc.decision. *)
Class DecEq (T : Type) :=
{
    eqdec : forall (a b :T), {a=b} + {a<>b}
}.

Notation "a =?= b " := (eqdec a b) (at level 69).



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
  simpl. auto.
Qed.


Definition toBool {A B : Prop} (sm: {A} + {B}) : bool :=
match sm with
| left _ => true
| right _ => false
end.

(* Local Coercion toBool : sumbool >->bool. *)

Require Import Coq.Unicode.Utf8.

Definition eq_existsT (A : Type)
                      (B : A → Prop)
                      (a a' : A)
                      (b : B a)
                      (b' : B a')
                      (ea : a = a')
                      (eb : match ea in _ = a' return B a' with eq_refl => b end = b')
  : exist B a b = exist B a' b'
  := match ea as ea
              in _ = a'
        return ∀ b' : B a',
                 match ea in _ = a' return B a' with eq_refl => b end = b'
                 → exist B a b = exist B a' b'
     with
       | eq_refl => fun b' eb => match eb with eq_refl => eq_refl (exist B a b) end
     end b' eb.

Require Import NPeano.

Instance nat_decidable : DecEq nat.
Proof.
  constructor.
  intros.
  destruct (NPeano.Nat.eq_dec (a) (b)) as [T|F];[left|right]; trivial.
Defined.


Definition opExtract {A : Type}
   (a : option A) (def: A ): A :=
match a with
| Some a' => a'
| None => def
end.

Definition assert (b : bool) : Prop := (b = true).
Coercion assert : bool >-> Sortclass.

Inductive void: Set :=.

(* Using typeclasses, this can be made to work for other types of products,
    e.g. propositional conjunctions 

  Notation π₁ := fst.
  Notation π₂ := snd.
*)

Definition subList {T : Type} (start length : nat) (l : list T) : list T :=
  firstn length (skipn start l).

Definition isPrefixOf {T : Type} (lp l : list T) : Prop :=
  firstn  (length lp) l =lp.

Definition substHead {A : Type} (l : list A) (h' : A) :=
match l with
| nil => nil
| h::tl => h'::tl
end.

Lemma  nth_error_map :
  ∀ (A B: Type) (f:A->B) 
     (n : nat) (l: list A),
      option_map f (nth_error l n) = 
        nth_error (map f l) n.
Proof.
  induction n; destruct l as [| h tl]; auto.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma  nth_error_nil :
  ∀ (A : Type) (n : nat), nth_error (@nil A) n = None.
Proof.
  induction n ;auto.
Qed.

Hint Rewrite nth_error_nil : Basics.

Lemma RemoveOrFalse : forall A , A \/ False <-> A.
Proof.
  tauto.
Qed.
Ltac repnd :=
  repeat match goal with
           | [ H : _ /\ _ |- _ ] =>
            let lname := fresh H "l" in 
            let rname := fresh H "r" in 
              destruct H as [lname rname]
         end.
Ltac dands :=
  repeat match goal with
           | [ |- _ /\ _ ] => split
           | [ |- prod _ _ ] => split
         end.


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

Require Import Omega.
Theorem comp_ind_type :
  ∀ P: nat → Type,
    (∀ n: nat, (∀ m: nat, m < n → P m) → P n)
    → ∀ n:nat, P n.
Proof.
 intros P H n.
 assert (∀ n:nat , ∀ m:nat, m < n → P m).
 intro n0. induction n0 as [| n']; intros.
 omega.
 destruct (eq_nat_dec m n'); subst; auto.
 apply IHn'; omega.
 apply H; apply X.
Qed.


Lemma BetterConj : ∀ (A B : Prop),
  A -> (A -> B) -> (A /\ B).
tauto.
Qed.

Ltac Dor H := destruct H as [H|H].

Ltac provefalse :=
  assert False ;[| contradiction].


Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" := 
  (@ltac_something _ _).

Lemma ltac_something_eq : forall (e:Type),
  e = (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_hide : forall (e:Type),
  e -> (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_show : forall (e:Type),
  (@ltac_something _ e) -> e.
Proof. auto. Qed.

Ltac show_hyp H :=
  apply ltac_something_show in H.

Ltac hide_hyp H :=
  apply ltac_something_hide in H.


Ltac show_hyps :=
  repeat match goal with
    H: @ltac_something _ _ |- _ => show_hyp H end.

Ltac Replace T :=
assert T as Heq by reflexivity; rewrite Heq; clear Heq.

Ltac ReplaceH T H :=
assert T as Heq by reflexivity; rewrite Heq in H; clear Heq.

Fixpoint search (n: nat) (f : nat → bool) : option nat :=
match n with
| O =>  None
| S n' => if (f n') 
            then Some n' 
            else search n' f
end.

Lemma searchSome : ∀ (f : nat → bool) (n m: nat) ,
  search n f = Some m → f m = true ∧ m < n .
Proof.
  induction n.
- intros ? Heq. simpl in Heq. inversion Heq.
- intros ? Heq. simpl in Heq.
  remember (f n) as fn.
  destruct fn.
  + inversion Heq. clear Heq.
    subst. auto.
  + apply IHn in Heq. split; try tauto.
    omega.
Qed.

Lemma searchNone : ∀ (n: nat) (f : nat → bool),
  search n f = None → ∀ m, m < n-> f m = false.
Proof.
  induction n; intros ? Heq; simpl in Heq.
- intros. omega.
- remember (f n) as fn.
  destruct fn.
  + inversion Heq.
  + intros ? Hlt.
    assert (m = n ∨ m < n) as Hd by omega.
    destruct Hd.
    * subst. auto.
    * auto.
Qed.

Lemma searchMax : ∀ (f : nat → bool) (b m c: nat) ,
  f c = true
  → c < b
  → search b f = Some m 
  → c <= m.
Proof.
  induction b; intros ? ? Heq Hlt Hs; simpl in Hs.
- inversion Hlt.
- remember (f b) as fn.
  destruct fn.
  + inversion Hs. clear Hs.
    subst. omega.
  + apply IHb; auto.
    assert (c = b ∨ c < b) as Hd by omega.
    destruct Hd; try congruence.
Qed.
