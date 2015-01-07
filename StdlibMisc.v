Require Import Coq.Lists.List.

Set Implicit Arguments.

Notation "x × y" := (prod x y) (at level 80, right associativity) : type_scope.

Definition ConjL (lp : list Prop) : Prop 
  := (fold_left (fun A B => A/\B) lp True).
 

Inductive Cast (T: Type) : Prop :=
cast : T -> Cast T.



Definition InjectiveFun {A B} (f : A -> B) :=
  forall (a1 a2: A), f a1 = f a2 -> a1 = a2.


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

