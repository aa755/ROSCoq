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

Require Import Vector.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import ackermannSteering.
Require Import MCMisc.tactics.
Require Import CartIR.
Require Import ackermannSteering.
Require Import fastReals.interface.
Require Import fastReals.misc.
Require Import geometry2D.
Require Import geometry2DProps.
Require Import ackermannSteeringProp.
Require Import MathClasses.orders.rings.
Require Import MathClasses.interfaces.orders.
Require Import ackermannSteeringProp.
Require Import IRMisc.LegacyIRRing.


Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.


Lemma nonTrivialCarDimPlausible : forall (cd : CarDimensions Q),
  nonTrivialCarDim cd
  -> plausibleCarDim ('cd).
Proof.
  unfold nonTrivialCarDim, plausibleCarDim.
  intros ? H. repnd;
  dands; simpl; apply preserves_nonneg; apply lt_le; assumption.
Qed.
  
  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).
  Local Notation  "∫" := Cintegral.
  
(** Many trignometric comparisons can be made easily
if the angles are in a fixed quadrant
For getting in/out of a parallel parked spot, a car's orientation does not
need to change by 90 degrees, even though the car moves
both forward and backward. So we assume that its
orientation remains in the first quadrant (between 0 and 90).
Assume that the X axis represents the road.
Now, it is easy to characterize the X Y extent of the car,
in terms of the coordinates of the four corners of the car*)
Section Rigid2DState.
  Variable cs :Rigid2DState IR.
  Variable cd :CarDimensions IR.
  Hypothesis nonTriv : plausibleCarDim cd.
  Hypothesis theta90 : 0 ≤ θ2D cs ≤ (½ * π).
  
  Lemma carBoundsAMAuxMin : 
    minCart (rightSideUnitVec cs * ' width cd) (- (rightSideUnitVec cs * ' width cd))
    = -('width cd) * {|X:= sin (θ2D cs); Y:= cos (θ2D cs)|}.
  Proof using All.
    destruct nonTriv as [a b]. destruct b as [c b].
    apply unitVecNonNeg in theta90.
    unfold unitVec in theta90.
    destruct theta90 as [x y]. simpl in x, y.
    unfold rightSideUnitVec. rewrite unitVecMinus90.
    unfold minCart. split; simpl;
    autounfold with IRMC.
    - rewrite Min_comm.
      rewrite leEq_imp_Min_is_lft;[ring|].
      rewrite <- cring_inv_mult_rht.
      apply mult_resp_leEq_rht;[| assumption].
      apply shift_leEq_rht. unfold cg_minus.
      rewrite cg_inv_inv.
      apply plus_resp_nonneg; assumption.

    - rewrite leEq_imp_Min_is_lft;[ring|].
      rewrite  cring_inv_mult_rht.
      apply inv_resp_leEq.
      rewrite <- cring_inv_mult_rht.
      apply mult_resp_leEq_rht;[| assumption].
      apply shift_leEq_rht. unfold cg_minus.
      rewrite cg_inv_inv.
      apply plus_resp_nonneg; assumption.
  Qed.

  (* only needed to replace leEq_imp_Min_is_lft by leEq_imp_Max_is_rht *)
  Lemma carBoundsAMAuxMax : 
    maxCart (rightSideUnitVec cs * ' width cd) (- (rightSideUnitVec cs * ' width cd))
    = ('width cd) * {|X:= sin (θ2D cs); Y:= cos (θ2D cs)|}.
  Proof using All.
    destruct nonTriv as [a b]. destruct b as [c b].
    apply unitVecNonNeg in theta90.
    unfold unitVec in theta90.
    destruct theta90 as [x y]. simpl in x, y.
    unfold rightSideUnitVec. rewrite unitVecMinus90.
    unfold maxCart. split; simpl;
    autounfold with IRMC.
    - rewrite Max_comm.
      rewrite leEq_imp_Max_is_rht;[ring|].
      rewrite <- cring_inv_mult_rht.
      apply mult_resp_leEq_rht;[| assumption].
      apply shift_leEq_rht. unfold cg_minus.
      rewrite cg_inv_inv.
      apply plus_resp_nonneg; assumption.

    - rewrite leEq_imp_Max_is_rht;[ring|].
      rewrite  cring_inv_mult_rht.
      apply inv_resp_leEq.
      rewrite <- cring_inv_mult_rht.
      apply mult_resp_leEq_rht;[| assumption].
      apply shift_leEq_rht. unfold cg_minus.
      rewrite cg_inv_inv.
      apply plus_resp_nonneg; assumption.
  Qed.

  Lemma carBoundsAMAuxMin2 : 
    minCart 
      ((- frontUnitVec cs * ' lengthBack cd)) 
      (frontUnitVec cs * ' lengthFront cd)
    =  -(frontUnitVec cs) * (' lengthBack cd).
  Proof using All.
    rewrite <- negate_mult_distr_l.
    rewrite negate_mult_distr_r.
    unfold frontUnitVec.
    setoid_rewrite <- sameXYNegate.
    setoid_rewrite unitVecMinDistr;[| assumption].
    fequiv.
    unfold cast, castCRCart2DCR. 
    fequiv.
    apply leEq_imp_Min_is_lft.
    apply shift_leEq_rht.
    unfold cg_minus. revert nonTriv.
    unfold plausibleCarDim.
    autounfold with IRMC.
    intros.
    rewrite cg_inv_inv.
      apply plus_resp_nonneg; tauto.
  Qed.

  Lemma carBoundsAMAuxMax2 : 
    maxCart 
      ((- frontUnitVec cs * ' lengthBack cd)) 
      (frontUnitVec cs * ' lengthFront cd)
    =  (frontUnitVec cs) * (' lengthFront cd).
  Proof using All.
    rewrite <- negate_mult_distr_l.
    rewrite negate_mult_distr_r.
    unfold frontUnitVec.
    setoid_rewrite <- sameXYNegate.
    setoid_rewrite unitVecMaxDistr;[| assumption].
    fequiv.
    fequiv.
    apply leEq_imp_Max_is_rht.
    apply shift_leEq_rht.
    unfold cg_minus. revert nonTriv.
    unfold plausibleCarDim.
    autounfold with IRMC.
    intros.
    rewrite cg_inv_inv.
      apply plus_resp_nonneg; tauto.
  Qed.
    
  Lemma carBoundsAMAux : carMinMaxXY cd cs =
  {|minxy := {|X:= X (backLeft cd cs); Y:= Y (backRight cd cs)|};
     maxxy := {|X:= X (frontRight cd cs); Y:= Y (frontLeft cd cs) |} |}.
  Proof using All.
  unfold carMinMaxXY.
  unfold backRight, backLeft.
  Local Opaque unitVec.
  simpl. unfold  boundingUnion.
  simpl. 
  Typeclasses eauto :=10.
  pose proof (minCartSum (pos2D cs - frontUnitVec cs * ' lengthBack cd)).
  unfold BoundingRectangle. simpl.
  Local Opaque minCart.
  Local Opaque maxCart.
  simpl. split; simpl.
  - rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).  
    rewrite (minCartSum _).
    rewrite carBoundsAMAuxMin.
    rewrite <- (@simple_associativity _ _ (@minCart IR _) _ _).
    unfold frontRight, frontLeft.
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).  
    rewrite minCartSum.
    rewrite (@commutativity _ _ _ (@minCart IR _) _ _ (rightSideUnitVec cs * ' width cd)).
    rewrite carBoundsAMAuxMin.
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite minCartSum.
    rewrite (@commutativity _ _ _ (@plus (Cart2D IR) _) _ _ 
      (-' width cd * {| X := sin (θ2D cs); Y := cos (θ2D cs) |})).
    rewrite (@commutativity _ _ _ (@plus (Cart2D IR) _) _ _ 
      (-' width cd * {| X := sin (θ2D cs); Y := cos (θ2D cs) |})).
    rewrite minCartSum. simpl.
    rewrite carBoundsAMAuxMin2.
    unfold rightSideUnitVec. rewrite unitVecMinus90.
    split; simpl; autounfold with IRMC; IRring.
  - 
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).  
      rewrite (maxCartSum _).
    rewrite carBoundsAMAuxMax.
    rewrite <- (@simple_associativity _ _ (@maxCart IR _) _ _).
    unfold frontRight, frontLeft.
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite  (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).  
    rewrite maxCartSum.
    rewrite (@commutativity _ _ _ (@maxCart IR _) _ _ (rightSideUnitVec cs * ' width cd)).
    rewrite carBoundsAMAuxMax.
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite <- (@simple_associativity _ _ (@plus (Cart2D IR) _) _ _).
    rewrite maxCartSum.
    rewrite (@commutativity _ _ _ (@plus (Cart2D IR) _) _ _ 
      (' width cd * {| X := sin (θ2D cs); Y := cos (θ2D cs) |})).
    rewrite (@commutativity _ _ _ (@plus (Cart2D IR) _) _ _ 
      (' width cd * {| X := sin (θ2D cs); Y := cos (θ2D cs) |})).
    rewrite maxCartSum.
    rewrite carBoundsAMAuxMax2.
    unfold rightSideUnitVec. rewrite unitVecMinus90.
    split; simpl; autounfold with IRMC; IRring.
  Qed.


  (** When the turn curvature is fixed, a car's position and orientation, and hence
   the position of its corners, and hence the confining axis-aligned rectangle,
   can be defined just as a function of initial state and the car's orientation.
    The lemma [carMinMaxXYAM] below proves the correctness of this definition..
  *)
   
  Definition carMinMaxXYAtθ  (init : Rigid2DState IR) (cd : CarDimensions IR)
        (turnRadius θ : IR) : Line2D IR :=  
  let θi := θ2D init in
  '(pos2D init) +
  {| minxy:= {|
      X := turnRadius * (sin θ - sin θi) - (width cd) * sin θ - (lengthBack cd) * cos  θ;
      Y := turnRadius * (cos θi - cos θ) - (width cd) * cos θ - (lengthBack cd) * sin  θ
        |};
     maxxy := {|
      X := turnRadius * (sin θ - sin θi) + (width cd) * sin θ + (lengthFront cd) * cos  θ;
      Y := turnRadius * (cos θi - cos θ) + (width cd) * cos θ + (lengthFront cd) * sin  θ
        |}
  |}.
  
  Global Instance ProperCarMinMaxAtθ : Proper
    (equiv ==> equiv ==> equiv ==> equiv ==> equiv) 
       carMinMaxXYAtθ.
  Proof using.
    intros ? ? H1e ? ? H2e ? ? H3e ? ? H4e.
    unfold carMinMaxXYAtθ. rewrite H1e.
    rewrite H2e. rewrite H3e.  rewrite H4e.
    reflexivity.
  Qed.
End Rigid2DState.

Require Import MathClasses.interfaces.vectorspace.

Section TurnMove.
  Variable cd :CarDimensions IR.
  

Definition carMinMaxXYAtθ2 (init : Rigid2DState ℝ)  (tr θ : ℝ) :=
let θi:=θ2D init in
' pos2D init +
{|
minxy := {|
  X := ⟨{|X:= - lengthBack cd; Y:= tr- width cd|}, unitVec θ⟩
          - tr * sin θi ;
  Y := ⟨{|X:= - tr - width cd; Y:= - lengthBack cd|},
          unitVec θ⟩ + tr * cos θi|};
maxxy := {| 
  X := ⟨{|X:= lengthFront cd; Y:= tr + width cd|}, unitVec θ⟩
          - tr * sin θi;
  Y := ⟨{|X:= - tr + width cd; Y:=  lengthFront cd|},
          unitVec θ⟩ + tr * cos θi |}
|}.

Definition carMinMaxXYAtθ3 (init : Rigid2DState ℝ)  (tr θ : ℝ) :=
let θi:=θ2D init in
' pos2D init - '(negY * ('tr) * unitVecT θi) +
{|
minxy := {|
  X := ⟨{|X:= - lengthBack cd; Y:= tr- width cd|}, unitVec θ⟩;
  Y := ⟨{|X:= - tr - width cd; Y:= - lengthBack cd|},unitVec θ⟩|};
maxxy := {| 
  X := ⟨{|X:= lengthFront cd; Y:= tr + width cd|}, unitVec θ⟩;
  Y := ⟨{|X:= - tr + width cd; Y:=  lengthFront cd|},unitVec θ⟩|}
|}.

Lemma carMinMaxXYAtθ2Same (init : Rigid2DState ℝ)  (tr θ : ℝ):
  carMinMaxXYAtθ2 init tr θ = carMinMaxXYAtθ init cd tr θ.
Proof using.
  unfold carMinMaxXYAtθ2, inprod, InProductCart2D.
  simpl. unfold carMinMaxXYAtθ.
  split;split;simpl; try IRring.
Qed.

Lemma carMinMaxXYAtθ3Same (init : Rigid2DState ℝ)  (tr θ : ℝ):
  carMinMaxXYAtθ3 init tr θ = carMinMaxXYAtθ init cd tr θ.
Proof using.
  rewrite <- carMinMaxXYAtθ2Same.
  split;split;simpl;IRring.
Qed.


  Section Plausible.  
  Hypothesis nonTriv : plausibleCarDim cd.

  Lemma carMinMaxXYAM : forall init tr θ,
  (0 ≤ θ ≤ (½ * π))
  ->
    carMinMaxXY cd (turnRigidStateAtθ init tr θ)
    = carMinMaxXYAtθ init cd tr θ.
  Proof using nonTriv.
    intros ? ? ? H90.
    rewrite carBoundsAMAux;[| assumption | exact H90].
    Local Opaque unitVec.
      simpl. unfold rightSideUnitVec.
      rewrite unitVecMinus90.
    Local Transparent unitVec. simpl. 
    rewrite foldPlusCart.
    split;split; simpl;
    IRring.
  Qed.
  End Plausible.
End TurnMove.

Require Import CartIR2.

Ltac proveFirstQuad :=
  rewrite PiBy2DesugarIR;
  rewrite <- (IRasCRasIR_id (Pi [/]TwoNZ));
  rewrite <- CRPiBy2Correct1;
  rewrite <- CRasIR0;
  apply CR_leEq2_as_IR;
  apply polarFirstQuad;
  match goal with
  [ntriv:nonTrivialCarDim _ |- _] => 
    apply nonTrivialCarDimPlausible in ntriv;
    unfold plausibleCarDim in ntriv;
    simpl in ntriv;
    do 3 rewrite inj_Q_nneg in ntriv;
    destruct ntriv as  [Ha Hbc]; destruct Hbc;
    split; simpl; autounfold with QMC; lra
  end.

Section TurnMoveQ.
  Variable cd :CarDimensions Q.
  Hypothesis ntriv : nonTrivialCarDim cd.

  Variable tr : Q.
  Let βMinusBack : Cart2D Q := βMinusBack cd tr.
  Let βMinusFront : Cart2D Q := βMinusFront cd tr.
  Let βPlusBack : Cart2D Q := βPlusBack cd tr.
  Let βPlusFront : Cart2D Q := βPlusFront cd tr.
  Let NegPosition : Type := bool (*outside*) * bool(*inside*).

  Definition minXYPos : (Cart2D ((Polar2D IR) * NegPosition)) :=
  {|X := ('βMinusBack,(true, true));
    Y := ('βPlusBack,(true, false))|}.

  Definition maxXYPos : (Cart2D ((Polar2D IR) * NegPosition)):=
  {|X := ('βPlusFront,(false, false)); 
    Y :=('βMinusFront,(true, true))|}.

  Definition minXYNeg : (Cart2D ((Polar2D IR) * NegPosition)):=
  {|X := ('βPlusBack,(true, false)); 
    Y := ('βMinusBack,(false, true))|}.


  Definition maxXYNeg : (Cart2D ((Polar2D IR) * NegPosition)):=
  {|X := ('βMinusFront,(false, true)) ; 
     Y :=('βPlusFront,(false, false))|}.

  Let negateIfTrue `{Negate A} (b:bool)(a:A) : A:=
    if b then (-a) else a.

  Definition decodeAsCos (nc: (Polar2D IR) * NegPosition) (theta:IR): IR :=
  let (c,n) := nc in
  let β :IR := θ c in
  let γ := theta + (negateIfTrue (negb (snd n)) β) in
    (negateIfTrue (fst n) ((rad c) * Cos γ)).

  Definition decodeAsCosXY (nc: Cart2D ((Polar2D IR) * NegPosition))
  (θ:IR): Cart2D IR :=
  let ync := (flipAngle (fst (Y nc)), snd (Y nc)) in
  {|X := decodeAsCos (X nc) θ;
    Y := decodeAsCos ync θ|}.

  Definition confineRectPos  (init : Rigid2DState IR) (θ:IR) : Line2D IR :=
  let θi := θ2D init in 
  '(pos2D init) -  '(negY * (''tr) * unitVecT θi) +
  {|
     minxy :=  decodeAsCosXY minXYPos θ ;
     maxxy := decodeAsCosXY maxXYPos θ  |}.

  Definition confineRectNeg (init : Rigid2DState IR) (θ:IR): Line2D IR:= 
  let θi := θ2D init in 
  '(pos2D init) + '(negY * (''tr) * unitVecT θi) +
   {|
     minxy :=  decodeAsCosXY minXYNeg θ ;
     maxxy := decodeAsCosXY maxXYNeg θ  |}.

  Lemma confineRectCorrect: ∀ (θ:IR) init,
    confineRectPos init θ = carMinMaxXYAtθ init ('cd) ('tr) θ
    /\ confineRectNeg init θ = carMinMaxXYAtθ init ('cd) ('-tr) θ.
  Proof using.
  intros.
  unfold confineRectPos, confineRectNeg.
  do 2 rewrite <- carMinMaxXYAtθ3Same.
  unfold decodeAsCosXY, decodeAsCos, carMinMaxXYAtθ3. simpl.
  fold CosClassIR SinClassIR.
  fold (@cos IR _) (@sin IR _).
  do 2 rewrite preserves_negate.
  do 1 rewrite negate_involutive.
  do 4 (rewrite <- unitVDot).
  do 4 (rewrite <- unitVDot2).
  do 8 (rewrite multDotRight).
  pose proof CartToPolarCorrect90Minus as Hr.
  unfold norm, NormCart2DQ in Hr.
  do 4 (rewrite <- Hr). clear Hr.
  pose proof CartToPolarCorrect as Hr.
  unfold norm, NormCart2DQ in Hr.
  do 4 (rewrite <- Hr). clear Hr.
  replace (@cast _ _ (@castCart Q IR _)) with (@castCart Q IR _);[| reflexivity].
  unfold castCart. simpl.
  pose proof  (@preserves_plus _ _ _ _ _ _ _ _ _ _ _ _
   (cast Q IR) _ tr) as Hh.
   unfold transpose.
   simpl.
  repeat rewrite Hh.
  rewrite  preserves_negate.
   unfold inprod, InProductCart2D;split; split; split; simpl;
    try IRring.
  Qed.

(** The turn center cannot be inside the car. for that,
one of the front wheels have to rotate by more than 90 along 
the vertical axis. 
*)
  Hypothesis turnCentreOut : (Qle (width cd) tr).
  
  Let trPos : (Qle 0 tr)%Q.
  Proof using.
    apply proj2, proj1 in ntriv.
    autounfold with QMC in ntriv.
    lra.
  Qed.
  
  Lemma firstQuadβMinusBack:
   (0:IR) ≤ ' polarTheta βMinusBack ≤  (½ * π).
  Proof using ntriv turnCentreOut.
    proveFirstQuad.
  Qed.
  
  Lemma firstQuadβPlusFront:
   (0:IR) ≤ ' polarTheta βPlusFront ≤  (½ * π).
  Proof using ntriv turnCentreOut.
    proveFirstQuad.
  Qed.
  
  Lemma firstQuadβPlusBack:
   (0:IR) ≤ ' polarTheta βPlusBack ≤  (½ * π).
  Proof using ntriv turnCentreOut.
    proveFirstQuad.
  Qed.
  
  
  Lemma firstQuadβMinusFront:
   (0:IR) ≤ ' polarTheta βMinusFront ≤  (½ * π).
  Proof using ntriv turnCentreOut.
  proveFirstQuad.
  Qed.
  
  (** cannot be Q, because after moving a move, the end position,
    which is the init position for the next
    move, can be a real number *) 
  Variable init: Rigid2DState IR.
  Hypothesis initFirstQuad : 0 ≤ (θ2D init) ≤ (½ * π).

  (* instead of modeling distance covered, we directly model the signed change in
    angle. distance = θd * tr.
    θd cannot be of type, because it's ideal value will be a solution of a trignometric
    equation, and there is no reason to expect the solution to be a rational 
  Variable θd: IR.*)
  
Require Import MathClasses.orders.semirings.
Require Import MCMisc.rings.

Let θi := (θ2D init).

  (** * Moving forward with positive turn radius
  * we will now characterize the monotonicity properties of each corner of the car
  *)

(*the car's leftmost point shifts right. *)
Lemma confineRectPosLeftDecreasing (θ: IR) :
θi ≤ θ ≤  (½ * π)
→ X (minxy (confineRectPos init θi)) ≤ X (minxy (confineRectPos init θ)).
Proof using turnCentreOut trPos ntriv initFirstQuad.
  simpl. intros Hb.
  apply (@order_preserving _ _ _ _ _ _ _ _).
  apply flip_le_negate.
  apply (@order_preserving _ _ _ _ _ _ _);
    [apply OrderPreserving_instance_0;
     apply Cart2DRadNNegIR |].
(*   apply firstQuadW1 in Hb; trivial ;[]. *)
  apply Cos_resp_leEq.
  - apply plus_resp_nonneg;[tauto|].
    apply firstQuadβMinusBack.
  - rewrite (divideBy2 Pi).
    apply plus_le_compat;[tauto| apply firstQuadβMinusBack].
  - apply plus_le_compat;[tauto| reflexivity].
Qed.

(*the car's rightmost point shifts right? *)
(*the car's bottommost point (closest to curb) shifts up if .... *)
(*the car's bottommost point shifts down, but at most by ...., if .... *)

  (** * Moving backward with negative turn radius
  * we will now characterize the monotonicity properties of each corner of the car
  *)

(* the rightmost point shifts left *)
Lemma confineRectNegLeftDecreasing (θ: IR) :
θi ≤ θ ≤  (½ * π) (* θ keeps increasing, because the negations cancel out *)
→ X (maxxy (confineRectNeg init θ)) ≤ X (maxxy (confineRectNeg init θi)).
Proof using turnCentreOut trPos ntriv initFirstQuad.
  simpl. intros Hb.
  apply (@order_preserving _ _ _ _ _ _ _ _).
  apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  apply Cos_resp_leEq.
  - apply plus_resp_nonneg;[|apply firstQuadβMinusFront].
    apply initFirstQuad.
  - rewrite (divideBy2 Pi).
    apply plus_le_compat;[|apply firstQuadβMinusFront].
    eapply transitivity;[apply Hb|]. reflexivity.
  - apply plus_le_compat;[tauto| reflexivity].
Qed.

End TurnMoveQ.
