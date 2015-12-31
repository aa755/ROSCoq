Require Import geometry2D.
Require Import Vector.
Require Import fastReals.misc.
Require Import MCInstances.
Require Import fastReals.interface.


Set Implicit Arguments.


Record ConicSection (A:Type):Type :=
{
  sqrCoeff : (Cart2D A);
  linCoeff : (Cart2D A);
  xyCoeff : A;
  constCoeff : A
}.


(**  The usual instances needed after defining a record type whose 
member types may have nonsyntactic equalities: *)

Global Instance EquivConicSection `{Equiv A} :
 Equiv (ConicSection A) := fun a b => (sqrCoeff a = sqrCoeff b) 
  /\ (linCoeff a = linCoeff b)
  /\ (xyCoeff a = xyCoeff b)
  /\ (constCoeff a = constCoeff b).

Global Instance EquivalenceCarDim  `{e:Equiv A}
  `{Equivalence _ e}
   : @Equivalence _ (@EquivConicSection _ _).
Proof using.
  unfold equiv, EquivConicSection. split.
  - intros x.
    auto with relations.
  - intros x y. destruct x,y. simpl. intros Hd; repnd;
      split; auto with relations.

  - intros x y z. destruct x,y,z. simpl. intros ? ?.
    repnd.
    split; eauto 3
    with relations.
Qed.

Global Instance ProperquadCoeff `{Equiv A} : 
Proper (equiv ==> equiv) (@sqrCoeff A).
Proof.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

Global Instance ProperlinCoeff `{Equiv A}: 
Proper (equiv ==> equiv) (@linCoeff A).
Proof.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

Global Instance ProperconstCoeff `{Equiv A} : 
Proper (equiv ==> equiv) (@constCoeff A).
Proof.
  intros ? ? Heq. destruct Heq. tauto.
Qed.


Section Conic.
(** A is the type of coefficients of the conic section.
We assume that it is an instance of a ring, and has an
[≤] instance which is a [orders.SemiRingOrder].
*)

Set Suggest Proof Using.

Context (A:Type) `{Ring A} `{Le A}
    `{@orders.SemiRingOrder A equiv plus mult zero one le}.

(*Move *)
Definition sqrEach : (Cart2D A) -> (Cart2D A) :=
@castCart A A (fun x => x*x). 

Require Import MathClasses.interfaces.vectorspace.

Definition evalConic (c : ConicSection A) (p : Cart2D A) :=
⟨sqrCoeff c, sqrEach p⟩ + ⟨linCoeff c, p⟩ 
+ (xyCoeff c) * (X p) * (Y p)
+ constCoeff c.

Require Import MathClasses.interfaces.additional_operations. 

(** B*B - 4*A*C*)
Definition discriminant (c : ConicSection A): A :=
  (xyCoeff c)^2 - 4* (X (sqrCoeff c)) * (Y (sqrCoeff c)).
  
End Conic.

Global Instance CastConicSection `{Cast A B} 
  : Cast (ConicSection A) (ConicSection B) :=
fun a =>  Build_ConicSection 
            ('sqrCoeff a)
            ('linCoeff a) 
            ('xyCoeff a)
            ('constCoeff a).
