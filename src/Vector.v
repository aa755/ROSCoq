Require Export Fin.

Set Implicit Arguments.


(*
Require Export PointWiseRing.
  FS_as_CSetoid (Fin n) T.
*)
Fixpoint Vector (n:nat) (T : Type)  : Type :=
match n with
| 0 => unit
| S n => (Vector n T) × T
end.

Definition VectInd {T} {P : forall n, Type}
 (bas: P 0)
 (rect: forall {n}, Vector n T -> P n ->  T -> P (S n)) 
 {m} (v : Vector m T): P m.
  induction m.
  - exact bas.
  - simpl in v. destruct v as [v t].
    exact (rect m v (IHm v) t).
Defined.


Definition vnth {T : Type} {m:nat} (v : Vector m T) (n : Fin m) : T.
  induction m;[apply f0; trivial| ].
  simpl in v. destruct n as [n np].
  destruct n; simpl in np.
  - exact (snd v).
  - apply fst in v. apply IHm;[exact v| ].
    exists n. apply sdjflksdjsdlkf3. trivial.
Defined.

(*
Definition isVecDerivativeOf 
    {n : nat} (f f' : Vector n TContR) : Type.
  revert f f'.
  induction n as [| np Hind]; intros f f';[exact unit|].
  destruct f as [fv ft].
  destruct f' as [fv' ft'].
  exact ((isDerivativeOf ft ft') × (Hind fv fv')).
Defined.
*)
Record Cart2D (T : Type) : Type := mkCart2D {X : T; Y: T}.
Record Polar2D (T : Type) : Type := mkPolar2D {rad : T; θ : T}.

Definition fromVec2D {T:Type}  (v2: Cart2D T) : Vector 2 T := (tt, X v2, Y v2).

Definition toVec2D {T:Type}  (v2: Vector 2 T) : Cart2D T  
  := {|X := snd (fst v2); Y:= (snd v2) |}.

(* copied from https://coq.inria.fr/library/Coq.Logic.ExtensionalityFacts.html#is_inverse *)
Definition is_inverse A B (f : A->B) (g : B -> A) 
  := (forall a:A, g (f a) = a) /\ (forall b:B, f (g b) = b).

Lemma toFromVecInv {T:Type}: @is_inverse (Cart2D T) _ fromVec2D toVec2D.
Proof.
  split; intro t; destruct t as [X Y];[reflexivity|].
  destruct X as [X XU]. destruct X.
  simpl. reflexivity.
Qed.

Coercion fromVec2D : Cart2D >-> Vector.
Coercion toVec2D : Vector >-> Cart2D.

Require Export CoRN.algebra.CRings.

Definition dotProduct {n:nat} {T : CRing} (vl vr : Vector n T) : T :=
@VectInd _ (fun n =>  Vector n T -> T) 
  (fun vr => [0]) 
  (fun  b _ rec tl vr =>  
              (tl [*]snd vr) [+] rec (fst vr)) n vl vr.

Require Export CanonicalNotations.
Require Import Coq.Unicode.Utf8.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.interfaces.abstract_algebra.

Instance castCart `{Cast A B} : Cast (Cart2D A) (Cart2D B) :=
  fun c => {|X := cast A B (X c) ;  Y := cast A B (Y c) |}.

Instance EquivCart  `{Equiv A} : Equiv (Cart2D A) :=
fun ca cb => (X ca = X cb /\ Y ca = Y cb).

Require Export StdlibMisc.

Instance Equivalence_instance_Cart2D2
  `{r: Equiv A} 
    `{Equivalence _ r} : @Equivalence (Cart2D A) equiv.
  unfold EquivCart. split.
  - intros x. destruct x. compute. split; auto with *.
  - intros x y. destruct x,y. compute. intros Hd; destruct Hd;
      split; auto with relations.

  - intros x y z. destruct x,y,z. compute. intros H0 H1.
    repnd.
    split; eauto 10
    with relations.
    rewrite H0l. auto.
    rewrite H0r. auto.
Qed.
 

Open Scope mc_scope.

Instance NormSpace_instance_Cart2D 
  (A B : Type) `{SqrtFun A B} 
  `{Plus A} `{Mult A} : NormSpace (Cart2D A) B :=
 λ (cart : Cart2D A), 
    (√((X cart) * (X cart) +  (Y cart) * (Y cart))).

Definition normSqr
  {A : Type}
  `{Plus A} `{Mult A} (cart : Cart2D A) : A  :=
    (((X cart) * (X cart) +  (Y cart) * (Y cart))).

Instance Zero_instance_Cart2D `{Zero A} : Zero (Cart2D A)
    := (({|X:=0 ; Y:=0|}))%mc.
Instance One_instance_Cart2D `{One A} : One (Cart2D A)
    := (({|X:=1 ; Y:=1|}))%mc.
Instance Plus_instance_Cart2D `{Plus A} : Plus (Cart2D A)
    := (λ a b, ({|X:= X a + X b ; Y:= Y a + Y b|}))%mc.
Instance Mutt_instance_Cart2D `{Mult A} : Mult (Cart2D A)
    := (λ a b, ({|X:= X a * X b ; Y:= Y a * Y b|}))%mc.
Instance Negate_instance_Cart2D `{Negate A} : Negate (Cart2D A)
    := (λ a, ({|X:= -(X a) ; Y:= -(Y a)|}))%mc.

Section Cart2DRing.

Require Export MathClasses.theory.rings.
Context `{Ring A}.


Add Ring  stdlib_ring_theoryldsjfsd : (rings.stdlib_ring_theory A).

Global Instance Ring_instance_Cart2D : Ring (Cart2D A).
  repeat(split);
  (repeat match goal with
  | [ H: Cart2D A |- _ ] => destruct H
  | [ H: equiv _ _ |- _ ] => unfold equiv, EquivCart in H; simpl in H; destruct H
  end);
  simpl; subst; eauto 2 with *; try ring; try( apply sg_op_proper; auto).
Qed.

Definition shiftOrigin (newOr pt : Cart2D A) :  Cart2D A :=
  pt - newOr.



Definition distSqr (a b : Cart2D A) : A :=
  normSqr (a - b ).

Global Instance Proper_Cart2DX :
     Proper  (equiv ==> equiv) (@X A).
  intros a b Heq.
  unfold equiv, EquivCart in Heq.
  repnd. assumption.
Defined.

Global Instance Proper_Cart2DY :
     Proper  (equiv ==> equiv) (@Y A).
  intros a b Heq.
  unfold equiv, EquivCart in Heq.
  repnd. assumption.
Qed.

Global Instance Proper_normSqr :
     Proper  (equiv ==> equiv) (@normSqr A _ _).
  intros a b Heq.
  unfold normSqr. rewrite Heq.
  reflexivity.
Qed.

Global Instance Proper_distSqr :
     Proper  (equiv ==> equiv ==> equiv) (@distSqr ).
  intros a b Heql c d  Heqr.
  unfold distSqr. 
  idtac. rewrite Heql, Heqr.
  reflexivity.
Qed.


End Cart2DRing.

Global Instance Cart2D_instance_le `{Le A}: Le (Cart2D A) :=
  λ p1 p2, (X p1 ≤ X p2) ∧ (Y p1 ≤ Y p2).

Definition sameXY {A} (a:A) : Cart2D A :=
  {|X :=a ; Y:= a|}.

Global Instance hjfkhskajhfksh  `{Equiv A} : Proper 
  (equiv ==> equiv ==> equiv) (@mkCart2D A).
Proof.
  intros ? ? Heq ? ? Hq.
  split; simpl; trivial.
Qed.

Global Instance ProperSameXY `{Equiv A}:
  Proper (equiv ==> equiv) (@sameXY A).
  intros a b Heq.
  split; auto.
Qed.

Lemma sameXYMult `{Ring A}: ∀ a b : A,
    sameXY a * sameXY b = sameXY (a * b).
Proof.
  intros. reflexivity.
Qed.

Lemma sameXYAdd `{Ring A}: ∀ a b : A,
     sameXY a + sameXY b = sameXY (a + b).
Proof.
  intros. reflexivity.
Qed.

Lemma sameXYNegate `{Ring A}: ∀ a : A,
  sameXY (-a) = - (sameXY a).
Proof.
  intros. reflexivity.
Qed.

Definition transpose {A:Type} (c: Cart2D A) :=
  {|X:= Y c; Y:= X c|}.


Lemma Cart2DEta `{Equiv A} `{Equivalence _ (@equiv A _)}  : forall c:Cart2D A,
   {| X:= X c; Y:=Y c |} = c.
Proof.
  intros. destruct c. simpl. reflexivity.
Qed.
