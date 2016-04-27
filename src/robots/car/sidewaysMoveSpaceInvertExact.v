(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)
(** printing ≡ $\equiv$ #≡# *)
(** printing [*] $*$ #*# *)
(** printing ∧ $\wedge$ #∧# *)
(** printing ∀ $\forall$ #∀# *)
(** printing → $\rightarrow$ #→# *)
(** printing ∃ $\exists$ #∃# *)
(** printing ≤ $\le$ #≤# *)
(** printing θ $\theta$ #θ# *)
(** printing eeev $\epsilon_v$ #∊ᵥ# *)
(** printing eeew $\epsilon_w$ #∊w# *)
(** printing tm $t_m$ #tm# *)
(** printing IR $\mathbb{R}$ #IR# *)
(** printing CR $\mathbb{R}$ #CR# *)
(** printing tr $t_r$ #tr# *)
(** remove printing * *)

(** printing ' $ $ #'# *)

Set Suggest Proof Using.

Require Import Vector.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import robots.car.ackermannSteering.
Require Import MCMisc.tactics.
Require Import CartIR.
Require Import fastReals.interface.
Require Import fastReals.misc.
Require Import geometry2D.
Require Import geometry2DProps.
Require Import robots.car.ackermannSteeringProp.
Require Import MathClasses.orders.rings.
Require Import MathClasses.interfaces.orders.
Require Import robots.car.atomicMoves.
Require Import IRMisc.LegacyIRRing.
Hint Unfold One_instance_IR : IRMC.
Require Import robots.car.firstQuadrant.

  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).
  Local Notation  "∫" := Cintegral.
  Local Notation ConfineRect := (Line2D).

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Require Import CartIR2.

Require Import robots.car.exampleDimensions.
Require Import robots.car.wriggle.
Require Import robots.car.sidewaysMove.


(** this file documents the failed efforts towards finding
a closed form solution to the problem of finding the parameters
for a given amount of available space for wriggle *)

Require Import conicSections.

Section ConicSection.

(**We will typically use the maximum turn curvature α, 
is based on the geometry of the car.*)
Variable α : Q.
Hypothesis αPos : ((0:IR)[<]'α).

(** Unlike α and cd, [d] will be determined from a solution to an optimization problem.
The ideal value may be irrational. Being forced to use a rational value may complicate
the proofs, and may foil the idea of dealing with inaccuracies separately. 
Making it a real number should not break proofs. This value is not needed in polar 
conversion. *)
Variable d : Q.

Variable cd : CarDimensions Q.
Hypothesis ntriv : nonTrivialCarDim (cd).
Hypothesis dNN : ((0:IR)≤'d).
Hypothesis firstQuadW: (0:IR) ≤ (2*'α*'d) ≤ ½ * π.
Local Notation tr := (Qinv α).


Let αNZ := ((pos_ap_zero _ _ αPos): 'α[#](0:IR)).


Local Definition trComplicated : 'tr = f_rcpcl ('α) αNZ.
Proof using αPos.
  apply QinvIRinv.
Qed.

(** The turn center cannot be inside the car. for that,
one of the front wheels have to rotate by more than 90 along 
the vertical axis. 
*)
Hypothesis turnCentreOut : (Qle (width cd) tr).


Definition BottomBoundCase1AsConic : ConicSection Q :=
{| 
  sqrCoeff := {|X:=0; Y:= - 2 * (tr - width cd) |};
  linCoeff := {|X:= - 2 *tr ; Y:= 0 |};
  xyCoeff := - 2 * lengthBack cd;
  constCoeff :=  2* tr -  width cd
|}.

Require Import MathClasses.interfaces.vectorspace.

Local Notation bottomBoundCase1 
  := (bottomBoundCase1 α d cd).

Lemma BottomBoundCase1AsConicCorrect :
  let θ :IR := (' α * ' d) in 
  bottomBoundCase1= 
  evalConic ('BottomBoundCase1AsConic) (unitVec θ).
Proof using αPos. 
  intro.
  hideRight.
  rewrite BottomBoundCase1Simpl; [|assumption].
  pose proof (unitVDouble (' α * ' d)) as Hh.
  rewrite  (@simple_associativity _ _ mult _ _ _) in Hh.
  rewrite Hh. clear Hh.
  subst. unfold evalConic,  sqrEach. simpl.
  unfold inprod, InProductCart2D.
  simpl. 
  fold θ.
  do 3 rewrite preserves_mult.
  do 2 rewrite preserves_plus.
  do 1 rewrite preserves_mult.
  do 3 rewrite preserves_negate.
  rewrite preserves_0.
  rewrite preserves_2.
  rewrite nat_pow.nat_pow_2.
  unfold cast.
  IRring.
Qed.

Let βMinusBack : Cart2D Q := (CornerAngles.βMinusBack cd tr).
Let βMinusFront : Cart2D Q := CornerAngles.βMinusFront cd tr.
Let βPlusBack : Cart2D Q := CornerAngles.βPlusBack cd tr.
Let βPlusFront : Cart2D Q := CornerAngles.βPlusFront cd tr.

(** 

The general solution for quartic equations is extremely horrendous:
https://upload.wikimedia.org/wikipedia/commons/9/99/Quartic_Formula.svg
It involves both square and cube roots.
It may be impossible to decide whether a root is real of imaginary, 
even though we started with rational coefficients.
Roots are nested. After taking a root, the decidability properties may be gone.
Only real roots are of use to us.

Delete? The conic exercise below seems to be useless, as the closed form solution remains
elusive.

The inverse probelem, i.e. to find the parameter d, given the available space
can be expressed as a problem of finding the intersection of a unit
circle with these conic sections, as suggested by Trold at:
http://math.stackexchange.com/questions/1593502/solving-a-sin-theta-b-cos-theta-c-sin-2-theta-d-cos-2-theta-k

There is a choice. Cos 2θ can be written in terms of either Sin^2 θ,
or Cos^2 θ, or both.
The rotation angle needed in each of these 3 cases seems to be the same.
But, in the last choice, it is immediately clear that the
asypmtotes of the hyperbola are orthogonal.
For the rotation angle in the Sin^2 θ case, look at the commit 
https://github.com/aa755/ROSCoq/commit/227e0d239723f7accbf58f4fdd6233645b6670e1
*)

(** Extra X space for available for wriggle *)
Variable  εwx : Q.
Hypothesis εwxNNeg : (0≤εwx).

Definition extraSpaceXWriggleAsConic : ConicSection Q :=
{| 
  sqrCoeff := negY * 'lengthBack cd;
  linCoeff := negY * βMinusFront;
  xyCoeff := 2 * (tr + width cd);
  constCoeff := - (totalLength cd + εwx)
|}.

Local Opaque inj_Q Q2R.

Local Notation extraSpaceXWriggleCase1 := 
(extraSpaceXWriggleCase1 α d cd).
(** We have to solve the inverse problem, which is LHS=0*)
Lemma extraSpaceXWriggleAsConicCorrect :
  let θ :IR := (' α * ' d) in 
  extraSpaceXWriggleCase1 - 'εwx= 
  evalConic ('extraSpaceXWriggleAsConic) (unitVec θ).
Proof using αPos.
  simpl.
  hideRight.
  unfold extraSpaceXWriggleCase1.
  rewrite rightExtraSpaceSimpl;[|assumption].
  unfold leftExtraSpaceTerm.
  subst. unfold evalConic,  sqrEach. simpl.
  unfold inprod, InProductCart2D.
  simpl.
  unfold totalLength.
  autorewrite with Q2RMC.
  unfold cast.
  fold (@ cast Q IR _).
  rewrite FFT3.
  IRring.
Qed.

(**Positive! Hence a hyperbola*)
Lemma extraSpaceXWriggleAsConicDiscriminant :
discriminant extraSpaceXWriggleAsConic = 
((2 * (tr + width cd)) ^ 2)%Q
+((2 * (lengthBack cd)) ^ 2)%Q.
Proof using.
  unfold discriminant.
  simpl.
  rewrite nat_pow.nat_pow_2.
  autounfold with QMC.
  simpl. ring.
Qed.


Lemma extraSpaceXWriggleRotateConicXYTerm :
rotateConicXYTerm extraSpaceXWriggleAsConic 
  = '(2:Q) * (nflip βPlusBack).
Proof using.
  unfold rotateConicXYTerm.
  simpl.
  split; simpl; autounfold with QMC; ring.
Qed.



Definition rotateConicXspaceArbitrary (θr:IR) : ConicSection IR:=
let pb : Polar2D IR := ' βPlusBack in
let pf : Polar2D IR := ' βMinusFront in
{|
sqrCoeff := negY * ' ((rad pb) * (cos (θ pb - 2 * θr)));
linCoeff := negY * ('(rad pf) * (unitVec (θ pf + θr)));
xyCoeff := 2 * (rad pb) * sin (θ pb - 2 * θr);
constCoeff := ' - (totalLength cd  + εwx) |}.

Lemma rotateConicXspace : forall (θr:IR),
(rotateConic θr ('extraSpaceXWriggleAsConic)) 
= rotateConicXspaceArbitrary θr.
Proof using.
  intros ?.
  unfold rotateConic, rotateConicXspaceArbitrary.
  rewrite <- (unitVDotRAsPolar βPlusBack).
  simpl.
  rewrite preserves_RotateConicXYTerm.
  rewrite extraSpaceXWriggleRotateConicXYTerm.
  rewrite (preserves_mult ('2) (nflip βPlusBack)).
  rewrite <-  castCartCommute.
  rewrite <- multDotLeft.
  rewrite unitVDotRAsPolarNflip.
  rewrite unitVDouble.
  do 2 rewrite nat_pow.nat_pow_2.
  rewrite FFT3.
  unfold inprod, InProductCart2D, nflip.
  simpl.
  split;[|dands]; simpl; try reflexivity; try IRring.
  - autorewrite with Q2RMC.
    split; simpl;  try IRring.
  - unfold unitVec. unfold mult, Mutt_instance_Cart2D.
    simpl.
    fold (@mult IR _).
    fold (@mult Q _).
    rewrite <- (unitVDotRAsPolarNegY βMinusFront).
    rewrite <- (unitVDotRAsPolarTranspose βMinusFront).
    unfold inprod, InProductCart2D, negY. simpl.
    autorewrite with Q2RMC. split; simpl; IRring.
  - rewrite preserves_2. IRring.
Qed.

Definition conicXspaceRotated : ConicSection IR:=
let pb : Polar2D IR := ' βPlusBack in
let pf : Polar2D IR := ' βMinusFront in
{|
sqrCoeff := '(rad pb) * negY ;
linCoeff := '(rad pf) * (unitVec (-(θ pf + ½ * θ pb)));
xyCoeff := 0; (** making this 0 was the main goal of rotation*)
constCoeff := ' - (totalLength cd  + εwx) |}.


Lemma conicXspaceRotatedCorrect:
  extraSpaceXWriggleCase1 - 'εwx =
  evalConic 
    conicXspaceRotated
    (unitVec (' α * ' d - ½ * 'polarTheta βPlusBack)).
Proof using αNZ.
  rewrite extraSpaceXWriggleAsConicCorrect.
  rewrite <- rotateConicCorrect2 with 
    (θ:= ½ * 'polarTheta βPlusBack).
  rewrite rotateAxisUnitVec.
  apply ProperEvalConic;[| reflexivity].
  rewrite rotateConicXspace.
  unfold rotateConicXspaceArbitrary.
  rewrite (@simple_associativity _ _ mult _ _).
  rewrite twoMultHalf.
  rewrite mult_1_l.
  simpl.
  rewrite plus_negate_r.
  rewrite Cos_zero.
  rewrite Sin_zero.
  setoid_rewrite mult_1_r.
  rewrite (@simple_associativity _ _ mult _ _).
  setoid_rewrite (@commutativity _ _ _ mult _ negY) at 2.
  rewrite <- (@simple_associativity _ _ mult _ _).
  rewrite <- unitVNegate.
  unfold conicXspaceRotated.
  split;[|dands]; simpl; try reflexivity; try IRring;
  split; simpl; try IRring.
Qed.


Local Notation βPlusBackNormSqrPos
:= (wriggle.βPlusBackNormSqrPos α cd ntriv).

Definition βPlusBackNormInv :IR :=
  normQIRInv  βPlusBack βPlusBackNormSqrPos.

Definition XspaceCircleCenter :=
let pb : Polar2D IR := ' βPlusBack in
let pf : Polar2D IR := ' βMinusFront in
'(½ * βPlusBackNormInv  * (rad pf))
        * (unitVec (θ pf + ½ * θ pb)).
        
Definition conicXspaceRotatedScaled : ConicSection IR:=
let pb : Polar2D IR := ' βPlusBack in
let pf : Polar2D IR := ' βMinusFront in
{|
sqrCoeff := negY; (**the goal here wasy make these +-1*)
linCoeff := negY * 2 * XspaceCircleCenter;
xyCoeff := 0;
constCoeff := βPlusBackNormInv * ' - (totalLength cd  + εwx) |}.

Lemma conicXspaceRotatedScaledCorrect : 
βPlusBackNormInv*(extraSpaceXWriggleCase1 - 'εwx) =
evalConic 
    conicXspaceRotatedScaled
    (unitVec (' α * ' d - ½ * 'polarTheta βPlusBack)).
Proof using αPos.
  rewrite conicXspaceRotatedCorrect.
  match goal with
  [|- context [unitVec ?k]] => generalize (unitVec k)
  end.
  intros ?.
  unfold βPlusBackNormInv, evalConic.
  simpl.
  unfold XspaceCircleCenter.
  rewrite unitVNegate. simpl.
  match goal with
  [|- context [unitVec ?k]] => generalize (unitVec k)
  end.
  intros c1.
  rewrite mult_0_l.
  rewrite mult_0_l.
  rewrite <- multDotLeft.
  rewrite <- multDotLeft.
  rewrite plus_0_r.
  rewrite plus_0_r.
  rewrite plus_mult_distr_l.
  rewrite (@simple_associativity _ _ mult _ _).
  rewrite <- QNormSqrIR.
  unfold normQIRInv.
  rewrite normIRInvSpecInvLeft.
  fold (normQIRInv βPlusBack βPlusBackNormSqrPos).
  fold βPlusBackNormInv.
  
  rewrite <- (@preserves_2 _ _ _ _ _ _ 
    _ _ _ _ _ _ (@cast IR (Cart2D IR) _) _).
  rewrite <- (@simple_associativity 
    IR _ mult _ ½ _ ).
  rewrite  (@simple_associativity 
    (Cart2D IR) _ mult _ _ _ ).
  rewrite (@preserves_mult _ _ _ _ _ _ 
    _ _ _ _ _ _  (@cast IR (Cart2D IR) _) _).
  rewrite  (@simple_associativity 
    (Cart2D IR) _ mult _ _ _ ).
  rewrite  <- (@simple_associativity 
    (Cart2D IR) _ mult _ negY _ ).
  rewrite <- (@preserves_mult _ _ _ _ _ _ 
    _ _ _ _ _ _  (@cast IR (Cart2D IR) _) _).
  rewrite twoMultHalf.
  rewrite preserves_1.
  rewrite mult_1_r.
  setoid_rewrite  <- (@commutativity 
    (Cart2D IR) _ _ mult _ _ negY ) at 2.
  rewrite  <- (@simple_associativity 
    (Cart2D IR) _ mult _ _ negY _ ).
  rewrite <- multDotLeft.
  IRring.
Qed.

Definition translateXConst : Q :=
 (Qmake 1 4) * ((normSqr βMinusFront)/ (normSqr βPlusBack)).

Definition XspaceStandardHyperbola : ConicSection IR:=
let pb : Polar2D IR := ' βPlusBack in
let pf : Polar2D IR := ' βMinusFront in
{|
sqrCoeff := negY;
linCoeff := 0; (** the goal here was to make this 0 by translating axes*)
xyCoeff := 0;
constCoeff := βPlusBackNormInv * (' - (totalLength cd  + εwx))
   - 'translateXConst * cos (2 * θ pf + θ pb)
|}.

Require Import MCMisc.rings.

Lemma conicXspaceStandardFormCorrect : forall (p:Cart2D IR),
evalConic conicXspaceRotatedScaled p
= 
evalConic 
    XspaceStandardHyperbola
    (p + XspaceCircleCenter).
Proof using.
  intro.
  unfold conicXspaceRotatedScaled.
  rewrite translateNegYConic.
  apply ProperEvalConic;[|reflexivity].
  split;[|dands]; simpl; try reflexivity;[].
  rewrite <- (@simple_associativity _ _ plus _ _ _ ).
  fequiv.
  rewrite  negate_swap_l.
  fequiv.
  unfold translateXConst.
  
  unfold sqr.
  fold (stdlib_rationals.Q_mult).
  fold (@mult Q _).
  rewrite (@preserves_mult _ _ _ _ _ _ 
      _ _ _ _ _ _  (@cast Q IR _) _).
  change (Qmake 1 4) with ((½ * ½):Q).
  rewrite (@preserves_mult _ _ _ _ _ _ 
      _ _ _ _ _ _  (@cast Q IR _) _).
  rewrite <- halfCorrectQR.
  assert (
  (2:IR)*(' polarTheta βMinusFront +
    ½ * ' polarTheta βPlusBack)
    = (2 * ' polarTheta βMinusFront +
   ' polarTheta βPlusBack)
    ) as H.
  - rewrite plus_mult_distr_l.
    rewrite (@simple_associativity _ _ mult _ _ _).
    rewrite twoMultHalf. IRring.
  - rewrite <- H. clear H.
    rewrite <- RingProp3.
    remember (' polarTheta βMinusFront +
    ½ * ' polarTheta βPlusBack).
    unfold sin, cos, SinClassIR, CosClassIR.
    setoid_rewrite <- Heqy. clear Heqy.
    pose proof (normRatioSqr βMinusFront βPlusBack) as H.
    setoid_rewrite H with (pb:=βPlusBackNormSqrPos).
    unfold βPlusBackNormInv.
    unfold sqr.
    autounfold with IRMC.
    rewrite Cos_plus.
    IRring.
Qed.


Lemma conicXspaceStandardFormCorrect2 : 
βPlusBackNormInv*(extraSpaceXWriggleCase1 - ' εwx) =
evalConic 
    XspaceStandardHyperbola
    (XspaceCircleCenter + unitVec (' α * ' d - ½ * 'polarTheta βPlusBack)).
Proof using αPos.
  rewrite conicXspaceRotatedScaledCorrect.
  rewrite (@commutativity (Cart2D IR) _ _ plus _ _).
  apply conicXspaceStandardFormCorrect.
Qed.

(**
The inverse problem, which is to find the value of [d], given 
the value of [εwx], has thus been reduced to the problem of 
finding the intersection of a unit-radius circle 
centered at [XspaceCircleCenter] and the hyperbola
[XspaceStandardHyperbola] which is in standard form.

Unfortunately, the solution still remains elusive.
We know that the Y coordinate of [XspaceCircleCenter] is positive,
but is not clear
whether its X coordinate is positive or negative, or whether
its distance from origin is less or greater than 1.
Also, it is not clear whether the hyperbola is symmetric along the X
axis or along the Y axis.
It depends on the sign of [constCoeff XspaceStandardHyperbola].
All these factors depend on the dimensions of the car.
*)
Lemma conicXspaceStandardFormCorrect3 : 
(extraSpaceXWriggleCase1 = 'εwx) 
↔
evalConic 
  XspaceStandardHyperbola
  (XspaceCircleCenter + unitVec (' α * ' d - ½ * 'polarTheta βPlusBack))
= 0.
Proof using αPos.
  rewrite <-conicXspaceStandardFormCorrect2.
  split; intro H;[rewrite H; IRring|].
  apply equal_by_zero_sum.
  apply mult_eq_zero in H;[apply H|].
  unfold βPlusBackNormInv.
  apply ap_imp_neq.
  apply f_rcpcl_resp_ap_zero.
Qed.

(** Check that angle 0 is a solution for the final hyperbola  for εwx=0*)
 
(**Positive! Hence a hyperbola*)
Lemma BottomBoundCase1AsConicDiscriminant :
discriminant BottomBoundCase1AsConic = 
((2 * lengthBack cd) ^ 2)%Q.
Proof using.
  unfold discriminant.
  simpl.
  rewrite mult_0_r.
  rewrite mult_0_l.
  rewrite minus_0_r.
  rewrite nat_pow.nat_pow_2.
  autounfold with QMC.
  simpl. ring.
Qed.

End ConicSection.
