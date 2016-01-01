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


Global Instance ProperxyCoeff `{Equiv A} : 
Proper (equiv ==> equiv) (@xyCoeff A).
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

Global Instance ProperSqrEach : 
Proper (equiv  ==> equiv) (@sqrEach).
Proof using H.
  intros ? ? h1.
  unfold  sqrEach, cast, castCart.
  simpl.
  unfold cast.
  rewrite h1.
  reflexivity.
Qed.

Require Import MathClasses.interfaces.vectorspace.

Definition evalConic (c : ConicSection A) (p : Cart2D A) :=
⟨sqrCoeff c, sqrEach p⟩ + ⟨linCoeff c, p⟩ 
+ (xyCoeff c) * (X p) * (Y p)
+ constCoeff c.


Global Instance ProperEvalConic : 
Proper (equiv ==> equiv ==> equiv) evalConic.
Proof using H.
  intros ? ? h1 ? ? h2.
  unfold evalConic, sqrEach.
  unfold cast, castCart, sqrEach.
  simpl.
  unfold cast.
  rewrite h1.
  rewrite h2.
  reflexivity.
Qed.

Require Import MathClasses.interfaces.additional_operations. 

(** B^2 - 4*A*C*)
Definition discriminant (c : ConicSection A): A :=
  (xyCoeff c)^2 - 4* (X (sqrCoeff c)) * (Y (sqrCoeff c)).

Definition conicAxisAligned (c : ConicSection A) :=
xyCoeff c = 0.

Definition rotateConicXYTerm  (cs : ConicSection A)  : Cart2D A :=
{| X := xyCoeff cs; Y := Y (sqrCoeff cs) - X (sqrCoeff cs) |}.

Definition rotateConic `{SinClass A} `{CosClass A} 
(θ:A) (cs : ConicSection A)  : ConicSection A :=
let a := X (sqrCoeff cs) in 
let c := Y (sqrCoeff cs) in 
let b := xyCoeff cs in 
{| 
  sqrCoeff := {|
    X:= a*(cos θ)^2 + b *(sin θ)*(cos θ)  + c*(sin θ)^2; 
    Y:= c*(cos θ)^2 - b *(sin θ)*(cos θ)  + a*(sin θ)^2;|};
  linCoeff := 
    {|X:= ⟨linCoeff cs, unitVec θ⟩; 
      Y:= ⟨nflip (linCoeff cs), unitVec θ⟩ |};
  xyCoeff := ⟨rotateConicXYTerm cs, unitVec (2*θ)⟩;
  constCoeff := constCoeff cs
|}.


End Conic.

Section ConicProps.

Require Import CartIR2.
Require Import geometry2DProps.
Require Import geometry2D.
Require Import CartIR.
Require Import IRMisc.LegacyIRRing.
Require Import fastReals.interface.

Local Opaque Sin.
Local Opaque Cos.
(* Move *)
Lemma FFT3 : forall (θ:IR),
cos θ * cos θ  = 1 - sin θ * sin θ.
Proof using.
  intro.
  rewrite <- (FFT θ).
  simpl.
  IRring.
Qed.

Lemma rotateConicCorrect : forall (θ:IR)
(cs : ConicSection IR)
(p : Cart2D IR) ,
evalConic (rotateConic θ cs)  p = evalConic cs (rotateAxis (-θ) p).
Proof using.
  intros ? ? ?.
  rewrite rotateAxisInvSimpl.
  unfold rotateConic, evalConic.
  simpl. rewrite unitVDouble.
  do 2 rewrite nat_pow.nat_pow_2.
  simpl.
  unfold rotateAxis, inprod, InProductCart2D.
  simpl.
  unfold cast.
  remember (sin θ) as s.
  remember (cos θ) as c.
  destruct cs.
  destruct sqrCoeff0.
  destruct linCoeff0.
  destruct p.
  simpl.
  rename xyCoeff0 into xy.
  rename constCoeff0 into cc.
  remember (fun x _ :IR => x*x) as sqr.
  (*ring_simplify takes all of the 16GB memory in a few seconds, and never returns.
    The current workaround is to change to a different ring.
    Both on Z, and any abstract MathClasses.abstract_algebra.ring,
    ring_simlify returns within a second.
    On Z, power terms are also reconized in the output.
    Here are the steps.
    1) remember all the non-ring terms. Express constants like 2,3
        inside the ring, e.g. 1+1, 1+1+1
    2) revert all variable to get a closed equality lemma. 
    3) Paste it in a new file containing  
        Require Import ZArith.
         Open Scope Z_scope.
    4) Replace ℝ by Z in the lemma statement.
        intros and then ring_simplify. Copy the simplified terms here and use
        ring to prove the correctness of the simplification. 
        Fortunately, unlike ring_simlify, ring works quickly.
    *)
  match goal with
  [|- ?l = _] => assert
  (l=
X * sqr c 2 * sqr X1 2 - 2 * X * c * s * X1 * Y1 +
X * sqr s 2 * sqr Y1 2 + sqr c 2 * Y * sqr Y1 2 + 
c * xy * s * sqr X1 2 - c * xy * s * sqr Y1 2 + 
2 * c * s * Y * X1 * Y1 + c * X1 * X0 + c * Y1 * Y0 -
2 * xy * sqr s 2 * X1 * Y1 + xy * X1 * Y1 + sqr s 2 * Y * sqr X1 2 +
s * X1 * Y0 - s * Y1 * X0 + cc )
  as Heq by  (subst sqr; simpl; clear ; IRring)
  end.
  rewrite Heq. clear Heq.

  match goal with
  [|- _ = ?l] => assert
  (l=
X * sqr c 2 * sqr X1 2 - 2 * X * c * s * X1 * Y1 +
X * sqr s 2 * sqr Y1 2 + sqr c 2 * xy * X1 * Y1 +
sqr c 2 * Y * sqr Y1 2 + c * xy * s * sqr X1 2 - 
c * xy * s * sqr Y1 2 + 2 * c * s * Y * X1 * Y1 + 
c * X1 * X0 + c * Y1 * Y0 - xy * sqr s 2 * X1 * Y1 +
sqr s 2 * Y * sqr X1 2 + s * X1 * Y0 - s * Y1 * X0 + cc )
  as Heq by  (subst sqr; simpl; clear ; IRring)
  end.
  rewrite Heq. clear Heq.
  subst.
  rewrite FFT3.
  IRring.
Qed.

Lemma rotateConicCorrect2 : forall (θ:IR)
(cs : ConicSection IR)
(p : Cart2D IR) ,
evalConic (rotateConic θ cs) (rotateAxis θ p) = evalConic cs p.
Proof using.
  intros.
  remember (rotateAxis θ p) as pp.
  rewrite <- (rotateAxisInvertibleIR p θ).
  subst pp.
  apply rotateConicCorrect.
Qed.

Global Instance CastConicSection `{Cast A B} 
  : Cast (ConicSection A) (ConicSection B) :=
fun a =>  Build_ConicSection 
            ('sqrCoeff a)
            ('linCoeff a) 
            ('xyCoeff a)
            ('constCoeff a).

Lemma multDotLeft `{Ring A}:
  ∀ (a:A) (b c : Cart2D A), a * (⟨ b, c ⟩) = ⟨ ' a * b, c ⟩.
Proof using.
  intros. unfold inprod, InProductCart2D.
  simpl.
  do 2 rewrite <- (@simple_associativity _ _ mult _ _).
  rewrite <- plus_mult_distr_l.
  reflexivity.
Qed.

Require Import geometry2D.
Require Import geometry2DProps.

(** The goal is to make it 0, and thus make the conic axis aligned*)
Lemma rotateConicXYCoeff : forall (θ:IR)
(cs : ConicSection Q),
let p : Polar2D IR := ' rotateConicXYTerm cs in
xyCoeff (rotateConic θ ('cs) )=  (rad p) * cos (Vector.θ p - 2 * θ).
Proof using.
  intros.
  hideRight.
  simpl.
  unfold rotateConicXYTerm.
  simpl.
  rewrite <- preserves_minus.
  change 
  ({| X := ' xyCoeff cs; Y := ' (Y (sqrCoeff cs) - X (sqrCoeff cs)) |})
  with
  (@cast _ (Cart2D IR) _ (rotateConicXYTerm cs)).
  rewrite CartToPolarCorrect.
  rewrite <- multDotLeft.
  rewrite unitVDot.
  subst.
  reflexivity.
Qed.

End ConicProps.


