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
  Hypothesis nonTriv : nonTrivialCarDim cd.
  Hypothesis theta90 : 0 ≤ θ2D cs ≤ (½ * π).
  
  Lemma carBoundsAMAuxMin : 
    minCart (rightSideUnitVec cs * ' width cd) (- (rightSideUnitVec cs * ' width cd))
    = -('width cd) * {|X:= sin (θ2D cs); Y:= cos (θ2D cs)|}.
  Proof using All.
    destruct nonTriv as [a b]. destruct b as [c b].
    apply unitVecNonNeg in theta90.
    unfold unitVec in theta90.
    destruct theta90 as [x y]. simpl in x, y.
    apply less_leEq in c.
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
    apply less_leEq in c.
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
    unfold nonTrivialCarDim.
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
    unfold nonTrivialCarDim.
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

Section TurnMove.
  Variable cd :CarDimensions IR.
  Hypothesis nonTriv : nonTrivialCarDim cd.
  
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

End TurnMove.
