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
Require Import atomicMoves.
Require Import IRMisc.LegacyIRRing.
Hint Unfold One_instance_IR : IRMC.

  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).
  Local Notation  "∫" := Cintegral.

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Section Wriggle.
(** * The Wriggle move
Now consider a 
#<href="https://rigtriv.wordpress.com/2007/10/01/parallel-parking/">wiggle motion</a>#
and characterize the the change in car's position and orientation caused
by this motion. 
The word "wriggle" was perhaps coined by Nelson in his 1967 book Tensor analysis.
Informally it denotes the following motion : 

  -steer (i.e rotate the steering wheel with brakes firmly pushed), 
  -drive (while keeping the steering wheel fixed),
  -reverse steer,
  -reverse drive

  Wiggle is parametrized by a nonzero [turnCurvature] and a drive distance,
  both of which may be signed.
  *)
Variable α : IR.
Hypothesis tcNZ : α[#]0.
Variable d : IR.
  
Local Notation turnRadius (*: IR *) := (f_rcpcl α tcNZ).
(** In our formalism, wriggle is a composition of the following 2 atomic moves.
  *)
  
Definition steerAndDrive : DAtomicMove:= 
  existT _ 
          {|am_tc := α; am_distance := d |} 
          (inr tcNZ).
  (*note that [revSteerAndrevDrive] is not the same as
  - steerAndDrive*)
Definition revSteerAndrevDrive : DAtomicMove :=
   existT _ 
     {|am_tc := -α; am_distance := -d |}
      (inr (tcnegNZ _ tcNZ)).
(** the distance covered during driving and 
  reverse driving is exactly the same.
  TODO: let them be slightly different, e.g. upto epsilon
 *)
Definition Wriggle : list DAtomicMove :=  
  [steerAndDrive; revSteerAndrevDrive].

(*
Add Ring tempRingIR : (stdlib_ring_theory IR).
 *)


Hint Unfold One_instance_IR : IRMC.

(** i, m, f respectively stand for initial, 
  middle, final
 *)

Lemma WriggleState : forall init,
  let θi := θ2D init in
  let θm := θi +  α * d in
  let θf := θi + 2 * α * d in
  let pf := pos2D init +
    (2*(unitVecT θm) - (unitVecT  θf) - (unitVecT θi))
    *{|X:=1;Y:=-1|}*'turnRadius in
  stateAfterAtomicMoves Wriggle init
  = {|pos2D := pf ; θ2D:= θf|}.
Proof using.
  intros ? ? ? ?. simpl.
  unfold stateAfterAtomicMove. simpl.
  split; simpl; [| subst  θi θm θf; simpl;
  IRring].
  rewrite reciprocalNeg with (xp:=tcNZ).
  fold Negate_instance_IR.
  fold (@negate IR _).
  assert 
    (θ2D init + α * d + - α * - d
    = θ2D init + 2 * α * d) as H by IRring.
  rewrite H.
  fold θi.
  fold θm.
  fold θf.
  split; simpl; try IRring.
Qed.

End Wriggle.

Section Sideways.


(** * The sideways move

Adding just one atomic move to the [SidewaysAux] move defined below
will get us to the sideways move. After [SidewaysAux],
as we will prove,
the car's orientation is same as that in the original state, but
it's position has shifted a bit, both along the car's orientaition and orthogonal to it.
[SidewaysAux] is just a straight-drive move inserted between
a wriggle and its inverse.
Note that without this insertion, we would have been back
to where we started.
*)
  Variable α : IR.
  Hypothesis tcNZ : α[#]0.
  Variable d : IR.
  Variable d' : IR.
  
  Local Notation SWriggle := (Wriggle α tcNZ d).
  
  Require Import commutator.
  (** Drive a distance of [ddistance]
    with front wheels perfectly straight.*)  
  Definition SidewaysAux : list DAtomicMove 
    := conjugate [mkStraightMove d'] SWriggle.

  
  (** The car's orientation at the end is same as that at the start.
     [θAtW] denotes the car's orientation at the completion of the [SWriggle] move. 
     For any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
     *)
  
  Definition sidewaysDisp (init : Rigid2DState ℝ) : Cart2D IR :=
     '(d') * unitVec ((θ2D init) + 2 * α * d).
     
  Lemma SidewaysAuxState : forall init,
  stateAfterAtomicMoves SidewaysAux init
  = {|pos2D := pos2D init 
      + sidewaysDisp init;
      θ2D := θ2D init |}.
  Proof using.
    intros.
    unfold SidewaysAux.
    rewrite straightConjugateState.
    rewrite WriggleState.
    simpl.
    reflexivity.
  Qed.

    Local Opaque conjugate.
    Local Opaque Wriggle.
  
  Definition sidewaysRect (w1rect : Line2D IR) (init : Rigid2DState ℝ) :=
  let w2rect := w1rect + 'sidewaysDisp init in
  boundingUnion w1rect w2rect.
  
  Lemma SidewaysAuxSpace :
  ∀  (cd : CarDimensions ℝ)
  (init : Rigid2DState ℝ)
  (w1rect: Line2D IR), 
carConfinedDuringAMs cd w1rect SWriggle init
-> carConfinedDuringAMs cd (sidewaysRect w1rect init) SidewaysAux init.
  Proof using.
    intros ? ? ?. simpl. intros H.
    eapply straightConjugateSpace with (d:=d')in H.
    rewrite WriggleState in H.
    simpl in H.
    exact H.
  Qed.

  (** After [SidewaysAux], the car is in the same orientation as before, but it has position
    has changed. For a sideways move, we just have drive straight to cancel
    the component of that position change along the car's orientation.
    We get this component by taking the dot product of the position change with the unit vector
    along the car's orientation.
    Formally, a sideways move is one where the car's position shifts in a direction
    orthogonal to its orientation.
    *)
  Local Notation DriveStraightRev 
    := (mkStraightMove (- d' * cos (2 * α * d))).

  Definition SidewaysMove : list DAtomicMove 
    := SidewaysAux ++ [DriveStraightRev].
    
  (** The car's final orientation is same as before, and 
  its position changes in the direction that is at a right angle [(½ * π)]
  to its orientation, i.e., it is a sideways move. 
  The distance moved is [ddistance * Sin  θw].

  As mentioned before, for any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
  *)

(* maybe delete from CartIR *)
Lemma unitVecLemma1 : forall θs θw:IR, 
  (unitVec (θs + θw)  - '(cos θw) * unitVec θs)
  = ('(sin  θw)) * unitVec (θs + (½ * π)).
Proof using.
  intros ? ?.
  unfold cast,castCRCart2DCR,
     sameXY, unitVec.   autounfold with IRMC.
  rewrite PiBy2DesugarIR.  
  rewrite Sin_plus_HalfPi.
  rewrite Cos_plus_HalfPi.
  simpl. split; simpl; autounfold with IRMC;
  [rewrite Cos_plus | rewrite Sin_plus]; try IRring.
Qed.

    Local Opaque SidewaysAux.
  Lemma SidewaysState : forall init,
  let θw := 2 * α * d  in
  stateAfterAtomicMoves SidewaysMove init
  = {|pos2D := pos2D init 
      + ('(d' * sin  θw)) * unitVec (θ2D init + (½ * π));
      θ2D := θ2D init |}.
  Proof using Type.
    intros ?.
    simpl.
    unfold SidewaysMove, mkStraightMove,
      stateAfterAtomicMoves.
    rewrite fold_left_app.
    simpl.
    fold stateAfterAtomicMoves.
    rewrite SidewaysAuxState.
    unfold stateAfterAtomicMove.
    simpl. unfold sidewaysDisp.
     rewrite mult_0_l, plus_0_r.
    split;[| reflexivity].
    simpl. 
    rewrite <- (@simple_associativity  _ _ plus _ _).
    fequiv.
    remember (2 * α * d) as θw. clear Heqθw.
    rewrite <- negate_mult_distr_l.
    rewrite  preserves_negate.
    rewrite  preserves_mult.
    rewrite negate_mult_distr_r.
    rewrite <- (@simple_associativity _ _ mult _ _ _).
    rewrite <- (@simple_distribute_l _ _  mult plus _ _ _ _).
    rewrite <- negate_mult_distr_l.
    rewrite unitVecLemma1.
    rewrite  preserves_mult.
     ring.
  Qed.
End Sideways.

Require Import firstQuadrant.

Section FirstQuadWriggle.
(**  The lemmas [SidewaysAuxSpace] above reduces
  the problem of computing the space needec by the
  [SidewaysAux] move to just doing that for the 
  [Wriggle] move, which constitutes the first 2 out
  of the 5 atomic moves in [SidewaysAux].
  WLOG, we consider the car's initial state to be ((0,0),0),
  which means it is at origin, and its forward direction
  points along the X axis.
  *)
Variable α : IR.
Hypothesis αPos : 0[<]α.
Variable d : IR.
Hypothesis dNN : 0≤d.
Hypothesis firstQuadW: 0 ≤ 2*α*d ≤ ½ * π.

Local Definition  adNN : 0≤α*d.
Proof using αPos dNN.
exact  (mult_resp_nonneg ℝ α d (less_leEq ℝ [0] α αPos) dNN).
Qed.

(*Local Lemma is not supported prior to 8.5beta3*)  
Local Definition firstQuadW1: ∀ θ : ℝ,
0 ≤ θ ≤ (α * d)
-> 0 ≤ θ ≤ ½ * π.
Proof using firstQuadW αPos  dNN.
  intros ? Hh.
  eapply inBetweenExpand; 
    [apply Hh |].
  clear Hh.
  split;[reflexivity|].
  eapply transitivity;[| apply firstQuadW].
  rewrite <- (@simple_associativity _ _ mult _ _ _).
  apply rings.RingLeProp2.
  apply adNN. 
Qed.
  
Local Definition firstQuadW2: ∀ θ : ℝ,
(α * d) ≤ θ ≤ 2*α * d
-> 0 ≤ θ ≤ ½ * π.
Proof using firstQuadW αPos  dNN.
  intros ? Hh.
  eapply inBetweenExpand; 
    [apply Hh |].
  clear Hh.
  split;[apply adNN|].
  tauto.
Qed.

Require Import MCMisc.rings.
Lemma adPiBy2:  α *  d ≤ ½ * Pi.
Proof using dNN firstQuadW αPos.
  eapply transitivity;[| apply firstQuadW].
  rewrite <- (@simple_associativity _ _ mult _ _).
  apply RingLeProp2.
  apply adNN; auto.
Qed.

Local Notation  αNZ := ((pos_ap_zero _ _ αPos): α[#]0).
Local Notation init  := (0:Rigid2DState IR).

Local Notation SWriggle := (Wriggle α αNZ d).

Local Notation tr := ((@f_rcpcl ℝ α (pos_ap_zero ℝ α αPos))).

Variable cd : CarDimensions ℝ.
Hypothesis nTriv : nonTrivialCarDim cd.
Lemma WriggleFirstQSpace :  ∀  (confineRect: Line2D IR),
  let sm:={|
       pos2D := ('tr) * {|
                   X := sin (α * d);
                   Y := (1 - cos (α * d))|} ;
          θ2D := α * d |} in
  (∀ θ : ℝ,
   (0 ≤ θ ≤ (α * d) 
      → carMinMaxXYAtθ 0 cd tr θ ⊆ confineRect)
   ∧ 
   (α * d ≤ θ ≤ (2* α * d)
    → carMinMaxXYAtθ sm cd (-tr) θ ⊆ confineRect))
  <->
  carConfinedDuringAMs cd confineRect SWriggle init.
Proof using All.
  intros ? ?. unfold Wriggle.
  (*to stop reduction*)
  match goal with
  [|- context [?h::nil]] => remember (h::nil) as hh
  end.
  simpl. subst hh.
  rewrite carConfinedDuringAMsSingle.
  simpl. unfold stateAfterAtomicMove.
  simpl. unfold confinedTurningAM. simpl.
(*  SearchAbout ((∀ a:?A, ?P a <-> ?Q a)). *)
  rewrite  conjunction_under_forall.
(*  SearchAbout ((∀ a:?A, ?P a /\ ?Q a)).  *)
  apply iff_under_forall.
  intro θ.
  match goal with
  [|- ?l ↔ _] => remember l as ll
  end.
  unfold inBetweenR.
  setoid_rewrite plus_0_l.
  setoid_rewrite plus_0_l.
  setoid_rewrite  reciprocalNeg with (xp:=αNZ).
  setoid_rewrite Sin_zero.
  setoid_rewrite Cos_zero.
  (*fold Zero_instance_IR.
  fold (@zero IR _).
  setoid_rewrite minus_0_r. *)
  setoid_rewrite cg_inv_zero.
  setoid_rewrite negate_mult_negate.
  setoid_rewrite leEq_imp_Min_is_lft;
    [| exact adNN
     | apply flip_le_minus_l; rewrite plus_negate_r
      ;exact adNN].
  setoid_rewrite leEq_imp_Max_is_rht;
    [| exact adNN
     | apply flip_le_minus_l; rewrite plus_negate_r
      ;exact adNN].
  fold (Le_instance_IR).
  fold (@le IR _).
  setoid_rewrite  (@commutativity _ _ _ mult _ _ tr).
  setoid_rewrite rings.RingProp3.
  setoid_rewrite  (@simple_associativity _ _ mult _ _ _).
  subst ll.
  apply and_iff_compat_lr.
  split;apply iff_under_imp;intros Hb;
  rewrite carMinMaxXYAM; try tauto;
  [apply firstQuadW1 | apply firstQuadW2]; assumption.
Qed.

Require Import MathClasses.interfaces.vectorspace.


(*
Add Ring tempRingIR : (stdlib_ring_theory IR).
*)

(** see [confineRect1] for a compact, but equivalent definition *)
Definition confineRect1Raw (θ:IR): Line2D IR
 := {|
   minxy := {|
             X := ⟨ {|
                    X := - lengthBack cd;
                    Y := tr - width cd |}, 
                  unitVec θ ⟩;
             Y := (⟨ {|
                     X := - tr - width cd;
                     Y := - lengthBack cd |}, 
                   unitVec θ ⟩) + tr |};
   maxxy := {|
           X := ⟨ {|
                  X := lengthFront cd;
                  Y := tr + width cd |}, 
                unitVec θ ⟩;
           Y := (⟨ {|
                   X := - tr + width cd;
                   Y := lengthFront cd |}, 
                 unitVec θ ⟩) + tr |} |}.

Definition confineRect2Raw (θ:IR): Line2D IR
 := ' (' tr * {| X := 2 * sin (α * d); 
                  Y := 1 - 2 * cos (α * d) |}) +
     {|
     minxy := {|
               X := (⟨ {|
                       X := - lengthBack cd;
                       Y := - tr - width cd |}, 
                     unitVec θ ⟩);
               Y := (⟨ {|
                       X := tr - width cd;
                       Y := - lengthBack cd |}, 
                     unitVec θ ⟩)|};
     maxxy := {|
             X := (⟨ {|
                     X := lengthFront cd;
                     Y := - tr + width cd |}, 
                   unitVec θ ⟩);
             Y := (⟨ {|
                     X := tr + width cd;
                     Y := lengthFront cd |}, 
                   unitVec θ ⟩)|} 
                   |}.


Lemma WriggleFirstQSpace2 :  ∀  (confineRect: Line2D IR),
(∀ θ:IR,
(0 ≤ θ ≤ α * d
 →  confineRect1Raw θ ⊆ confineRect)
∧ (α * d ≤ θ ≤ 2 * α * d
   → confineRect2Raw θ
     ⊆ confineRect))
  <->
  carConfinedDuringAMs cd confineRect SWriggle init.
Proof using All.
  intros ?. unfold confineRect1Raw, confineRect2Raw.
  rewrite <- WriggleFirstQSpace.
  apply iff_under_forall.
  intro θ.
  remember (f_rcpcl α (pos_ap_zero ℝ α αPos)) as trr.
  clear Heqtrr.
  apply and_iff_compat_lr.
  eapply andWeakenL.
  exact (@iff_under_imp2 _ _ _).
  apply and_comm.
  eapply andWeakenL.
  exact (@iff_under_imp2 _ _ _).
  eapply andWeakenL.
  apply po_properL; eauto with typeclass_instances.
  apply and_comm.
  eapply andWeakenL.
  apply po_properL; eauto with typeclass_instances.
  rewrite <- carMinMaxXYAtθ2Same.
  rewrite <- carMinMaxXYAtθ2Same.
  unfold carMinMaxXYAtθ2.
  simpl.
  rewrite Sin_zero.
  rewrite Cos_zero.
  fold Zero_instance_IR.
  fold (@zero IR _).
  fold One_instance_IR.
  fold (@one IR _).
  rewrite preserves_0.
  unfold inprod, InProductCart2D;split; split; split; simpl;
    try IRring.
Qed.


End FirstQuadWriggle.


(** 
In the above lemma [WriggleFirstQSpace2] each of
the 8 coordinates were of the form <..,unitVec θ>.
So, it was a linear some of sine and cosine of θ.
As θ varies, it is hard to find when it achieves an extrema.
Using Cartesian to polar conversion, each of the above
coordinate can be represemnted in the form
c1*cos(θ+β)+c2, where c1 and c2 are constants,
and β is an angle in the first quadrant.
It is much easier to characterize the extremas in this
representation. For example cosine of 0 is 1, and it decreases from 0 to π.

Because cartesian to polar conversion is currently
    only defined for rational coordinates, we now
    assume that the turn radius and the car's dimensions
    are rationals.
    Eventually, they can be reals 
    along with constructive proofs of whether
    they are 0 or away from it.

In the  "constant times cosine" explained above, the value 
in the representation, the angle β can for
the 4 coordinates can only take one of the following
4 values, or ½ * π -  one of these values: *)

Require Import robots.car.exampleDimensions.

Module CornerAngles.
Section CornerAngles.

Variable cd : CarDimensions Q.
Variable tr: Q.

Definition βMinusBack :(Cart2D Q) :=
({|X :=  lengthBack cd; Y := tr - width cd |}).

Definition βPlusBack :(Cart2D Q) :=
({|X :=  lengthBack cd; Y := tr + width cd |}).

Definition βMinusFront :(Cart2D Q) :=
( {|X :=  lengthFront cd; Y := tr - width cd |}).

Definition βPlusFront :(Cart2D Q) :=
( {|X :=  lengthFront cd; Y := tr + width cd |}).

End CornerAngles.
End CornerAngles.


Section FirstQuadWriggleQ.

Variable α : Q.
Hypothesis αPos : ((0:IR)[<]'α).
Variable d : Q.
Variable cd : CarDimensions Q.
Hypothesis ntriv : nonTrivialCarDim (' cd).
Hypothesis dNN : ((0:IR)≤'d).
Hypothesis firstQuadW: (0:IR) ≤ (2*'α*'d) ≤ ½ * π.
Local Definition tr := ((Qinv α):Q).


Let αNZ := ((pos_ap_zero _ _ αPos): 'α[#](0:IR)).


Local Definition trComplicated : 'tr = f_rcpcl ('α) αNZ.
Proof using αPos.
  pose proof αPos as Hh.
  eapply less_wdl in Hh;[|symmetry;apply inj_Q_Zero].
  apply less_inj_Q in Hh. simpl in Hh.
  assert (tr == Qdiv 1 α)%Q as H by (unfold tr;field;lra).
  rewrite H. setoid_rewrite inj_Q_div with (H:=αNZ).
  unfold cf_div.
  rewrite  inj_Q_One.
  unfold cast, Cast_instace_Q_IR.
  unfold Q2R.
  IRring.
Qed.

(** The turn center cannot be inside the car. for that,
one of the front wheels have to rotate by more than 90 along 
the vertical axis. 
*)
Hypothesis turnCentreOut : (Qle (width cd) tr).

(*not in use anymore?*)
Definition negY `{One A}`{Negate A} : Cart2D A:= 
{|X:=1;Y:=-1|}.


Definition NegPosition : Type := bool (*outside*) * bool(*inside*).



Require Import CartIR2.

Local Definition βMinusBack : Cart2D Q := CornerAngles.βMinusBack cd tr.
Local Definition βMinusFront : Cart2D Q := CornerAngles.βMinusFront cd tr.
Local Definition βPlusBack : Cart2D Q := CornerAngles.βPlusBack cd tr.
Local Definition βPlusFront : Cart2D Q := CornerAngles.βPlusFront cd tr.

Definition minXY1 : (Cart2D ((Polar2D IR) * NegPosition)) :=
{|X := ('βMinusBack,(true, true));
  Y := ('βPlusBack,(true, false))|}.

Definition maxXY1 : (Cart2D ((Polar2D IR) * NegPosition)):=
{|X := ('βPlusFront,(false, false)); 
  Y :=('βMinusFront,(true, true))|}.


Definition minXY2 : (Cart2D ((Polar2D IR) * NegPosition)):=
{|X := ('βPlusBack,(true, false)); 
  Y := ('βMinusBack,(false, true))|}.


Definition maxXY2 : (Cart2D ((Polar2D IR) * NegPosition)):=
{|X := ('βMinusFront,(false, true)) ; 
   Y :=('βPlusFront,(false, false))|}.


Definition negateIfTrue `{Negate A} (b:bool)(a:A) : A:=
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

Local Notation init  := (0:Rigid2DState IR).
Local Notation SWriggle := (Wriggle ('α) αNZ ('d)).

Local Definition trr :IR := 'tr.

Definition constW1 := {|X := 0; Y := trr|}.

Definition constW2 := (' trr * {| X := 2 * Sin ('α * 'd); 
                  Y := 1 - 2 * Cos ('α * 'd) |}).

Definition confineRect1 (θ:IR): Line2D IR
 := 'constW1 +
 {|
     minxy :=  decodeAsCosXY minXY1 θ ;
     maxxy := decodeAsCosXY maxXY1 θ  |}.

Definition confineRect2 (θ:IR): Line2D IR
 := 'constW2 +
 {|
     minxy :=  decodeAsCosXY minXY2 θ ;
     maxxy := decodeAsCosXY maxXY2 θ  |}.

Lemma confineRectCorrect: ∀ θ:IR,
confineRect1 θ = confineRect1Raw ('α) αPos ('cd) θ
/\ confineRect2 θ = confineRect2Raw ('α) αPos ('d) ('cd) θ.
Proof using.
  intro.
  unfold confineRect1, confineRect2, confineRect1Raw, confineRect2Raw.
  unfold decodeAsCosXY, decodeAsCos. simpl.
  fold CosClassIR SinClassIR.
  fold (@cos IR _) (@sin IR _).
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
  fold αNZ.
  repeat rewrite <- trComplicated.
  fold trr.
   unfold inprod, InProductCart2D;split; split; split; simpl;
    try IRring.
Qed.


(** Now lets consider all 4 sides one by one. They are
too different to handle simulaneously *)

Definition isBoundLeftWriggle1 (minx: IR) :=
forall θ:IR,
(0 ≤ θ ≤ 'α * 'd
 → minx ≤ X (minxy (confineRect1 θ))).

Definition isBoundLeftWriggle2 (minx: IR) :=
forall θ:IR,
('α * 'd ≤ θ ≤ 2 * 'α * 'd
   → minx ≤ X (minxy (confineRect2 θ))).

Definition isBoundLeftWriggle (minx: IR) :=
isBoundLeftWriggle1 minx
∧ isBoundLeftWriggle2 minx.



Ltac proveFirstQuad :=
  rewrite PiBy2DesugarIR;
  rewrite <- (IRasCRasIR_id (Pi [/]TwoNZ));
  rewrite <- CRPiBy2Correct1;
  rewrite <- CRasIR0;
  apply CR_leEq2_as_IR;
  apply polarFirstQuad;
  unfold nonTrivialCarDim in ntriv;
  simpl in ntriv;
  do 3 rewrite inj_Q_nneg in ntriv;
  destruct ntriv as  [Ha Hbc]; destruct Hbc;
  split; simpl; autounfold with QMC; lra.

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

Require Import MathClasses.orders.semirings.
Require Import MCMisc.rings.
(**During the first of the 2 atomic moves of Wriggle,
  the car's leftmost point shifts right. Hence, the 
  leftmost position of the leftmost point of the car
  occurs at the starting position. So we can ignore the
  rest of the move while analyzing the extra space needed
  on the left side.*)
Lemma confineRect1LeftMonotoneRight (minx β: IR) :
minx ≤ X (minxy (confineRect1 β))
→ 0 ≤ β ≤  (½ * π)
→ (forall θ:IR,
    β ≤ θ ≤  (½ * π) (* 'α * 'd *)
     → minx ≤ X (minxy (confineRect1 θ))).
Proof using firstQuadW ntriv turnCentreOut. 
  simpl.
  setoid_rewrite plus_0_l.
  intros Hh Hbb ? Hb.
  apply flip_le_negate.
  rewrite negate_involutive.
  apply flip_le_negate in Hh.
  rewrite negate_involutive in Hh.
  eapply transitivity;[| apply Hh].
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

Require Import CartIR.
Require Import IRTrig.
Require Import CoRNMisc.




(** The second move is much more difficult to analyse 
w.r.t the leftmost point. The leftmost position
of the leftmost point of the car can be at:

1) beginning of the move : if the car's rear plane is far away from the line joining the rear wheels (i.e. [lengthBack] is large), e.g. when a large 
rigid trailer is attached to the back of the car.

2) somewhere in the middle of the move

3) at the end of the move, assuming usual dimensions of
a car with no rear attachments.

It turns that the earlier hypothesis that the car needs
to turn by atmost 90 degrees while coming out of the parallel
parking was too conservative. Pictorial inuition seems
to suggest that the car need not turn by more than
[polarTheta βPlusFront].

onenote:https://d.docs.live.net/946e75b47b19a3b5/Documents/PhD6/ParallelParking.one#...into%203=%20to%20two&section-id={13BDE595-ACF2-4791-AAFC-6284FF953450}&page-id={670C8178-E541-483C-91A7-35F29052CCF3}&end

This is because because from that angle to 90 degrees,
the car's space requirement along the left, right and
bottom sides seem to decrease.

If so, assuming 
that [lengthBack ≤ lengthFront] implies that
the 3rd case will always hold.
 *)

Definition isMaxTurnNeeded (θmax : IR) :=
∀ (minx maxx miny: IR),
(minx ≤ X (minxy (confineRect1 θmax))
/\ miny ≤ Y (minxy (confineRect1 θmax))
/\ X (maxxy (confineRect1 θmax)) ≤ maxx
)
→ (∀ θ:IR,
    θmax ≤ θ ≤ ½ * π
     → 
    (minx ≤ X (minxy (confineRect1 θ))
    /\ miny ≤ Y (minxy (confineRect1 θ))
    /\ X (maxxy (confineRect1 θ)) ≤ maxx
    )
     ).
     

Local Opaque confineRect1.
Definition extraHyp1 : Prop := 
((½ * π ) ≤ (' polarTheta βPlusFront + ' polarTheta βPlusBack)).
Lemma maxTurnNeededConjecture (minx maxx miny: IR) :
extraHyp1
→
isMaxTurnNeeded ('polarTheta βPlusFront).
Proof using firstQuadW ntriv turnCentreOut.
  intro Has. unfold extraHyp1 in Has. simpl.
  intros ? ? ? H ? Hb.
  split;[| split].
  - eapply confineRect1LeftMonotoneRight;
      [ | | apply Hb];[tauto | ].
    apply firstQuadβPlusFront.
  - apply proj2 in H. apply proj1 in H.
    revert H.
Local Transparent confineRect1.
    unfold confineRect1. simpl.
    rewrite <- (negate_swap_r _ (½ * π )).
    rewrite (@simple_associativity _ _ plus _ _ ).
    rewrite (@simple_associativity _ _ plus _ _ ).
    rewrite CosMinusSwap.
    setoid_rewrite CosMinusSwap at 2.
    rewrite PiBy2DesugarIR.
    setoid_rewrite Cos_HalfPi_minus.
    intros Hh.
    eapply transitivity;[apply Hh|].
    apply (@order_preserving _ _ _ _ _ _ _ _).
    apply flip_le_negate.
    apply (@order_preserving _ _ _ _ _ _ _);
    [apply OrderPreserving_instance_0;
      apply Cart2DRadNNegIR |].
    clear Hh.
    rewrite <- Pi_minus_Sin.
    setoid_rewrite <- Pi_minus_Sin at 2.
    apply Sin_resp_leEq.
    + eapply transitivity;[apply MinusPiBy2Le0|].
      apply flip_le_minus_l.
      rewrite negate_involutive.
      setoid_rewrite plus_0_l.
      rewrite (divideBy2 Pi).
      apply plus_le_compat; [tauto| apply
        firstQuadβPlusBack].
    + apply flip_le_minus_l.
      rewrite commutativity.
      apply flip_le_minus_l.
      eapply transitivity;[| apply Has].
      apply eq_le.
      rewrite (divideBy2 π) at 1.
      rewrite PiBy2DesugarIR.
      IRring.
    + apply (@order_preserving _ _ _ _ _ _ _ _).
      apply flip_le_negate.
      rewrite commutativity.
      setoid_rewrite commutativity at 2.
      apply (@order_preserving _ _ _ _ _ _ _ _).
      tauto.
  - apply proj2 in H. apply proj2 in H.
    revert H.
    unfold confineRect1. simpl.
    rewrite plus_0_l.
    rewrite plus_0_l.
    intros Hh.
    eapply transitivity;[|apply Hh].
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
    clear Hh.
    rewrite plus_negate_r.
    rewrite Cos_zero. apply Cos_leEq_One.
Qed.

(** intuitively, it says that while turning left
at min radius, the rightmost position of the rightmost
point of the car is achieved after the bottommost
position of the bottommost point of the car is achieved.*)
Lemma hypothesisInAboveConjecture :
((lengthBack cd)/(tr + width cd)≤(tr + width cd)/(lengthFront cd))%Q
-> extraHyp1.
Abort.

(**This is definitely true for the geometry of Mazda 3 sedan*)

Definition thisCarHasSameGeometryAs (cg : CarGeometry Q) :=
  cd ≡ carDim cg /\ tr ≡ minTR cg.

(* Move *)
Lemma PiBy2IRCR:
CRasIR (½ * π) =  ½ * π.
Proof using.
  rewrite PiBy2DesugarIR.
  rewrite <- (IRasCRasIR_id (Pi [/]TwoNZ)).
  rewrite <- CRPiBy2Correct.
  rewrite commutativity.
  reflexivity.
Qed.

Lemma Mazda3Hyp1True :
thisCarHasSameGeometryAs ('Mazda3Sedan2014sGT)
-> extraHyp1.
Proof using.
  intro H.
  unfold extraHyp1.
  rewrite <- PiBy2IRCR.
  unfold cast, Cart_CR_IR.
  setoid_rewrite <- CR_plus_asIR.
  apply CR_leEq_as_IR.
  unfold βPlusFront, βPlusBack.
  destruct H as [Hl Hr].
  subst.
  rewrite Hr. clear Hr.
  apply CRweakenLt.
  unfold lt, CRlt. exists 1%nat.
  simpl. vm_compute. reflexivity.
Qed.

(** In fact, it is true by a large margin; Not only is it greater than
half pi, it is also greater than quarter 72/100 Pi. 
On the other hand, it is less than  75/100 Pi.
*)
Lemma Mazda3Hyp1TrueByLargeMargin :
thisCarHasSameGeometryAs ('Mazda3Sedan2014sGT)
-> (('(Qmake 72 100) * π ) < ( polarTheta βPlusFront +  polarTheta βPlusBack)).
Proof using.
  intro H. destruct H as [Hl Hr].
  unfold βPlusFront, βPlusBack.
  subst.
  rewrite Hr. clear Hr.
  unfold lt, CRlt. exists 4%nat.
  simpl. vm_compute. reflexivity.
Qed.


(** this version may not need any additional hypothesis,
  but it may not be strong enough for the remaining proofs. *)
Lemma conjecture2 :
isMaxTurnNeeded (Max ('polarTheta βPlusFront)
((½ * π ) - 'polarTheta βPlusBack)).
Abort.

(** Note that [lengthFront] and [lengthBack]
    are measured w.r.t the line joining the 2 rear wheels.
    This is a reasonable assumption for a car without
    any rear attachments. *)
Hypothesis lengthFrontGreater:
  (lengthBack cd <= lengthFront cd)%Q.

(**This assumption is innocuous. Perhaps [le] can be
replaced by [lt] in the definition of [nonTrivialCarDim],
so that this wont be needed.*)
Hypothesis ntrivStrict :
(0 < lengthFront cd /\ 0 < lengthBack cd)%Q.

(** This is a direct consequence of the above hypothesis
  [lengthFrontGreater] *)
Lemma FrontLeBack : 
  (' polarTheta βPlusFront) ≤ (' polarTheta βPlusBack).
Proof using firstQuadW lengthFrontGreater ntriv ntrivStrict turnCentreOut.

  unfold cast, Cart_CR_IR.
  apply CR_leEq_as_IR.
  apply polarFirstQuadMonotone; simpl;
  autounfold with QMC; [tauto| tauto|].
  unfold nonTrivialCarDim in ntriv. simpl in ntriv.
  do 3 (rewrite inj_Q_nneg in ntriv).
  apply Q.Qmult_le_compat_l;[| lra].
  apply  Q.Qdiv_flip_le; lra.
Qed.

Lemma βPlusMinusBack : 
'(polarTheta βMinusBack) ≤ cast CR IR (polarTheta βPlusBack).
Proof using firstQuadW ntriv ntrivStrict. 
  unfold cast, Cart_CR_IR.
  apply CR_leEq_as_IR.
  apply polarFirstQuadMonotone; simpl;
  autounfold with QMC; [tauto| tauto|].
  unfold nonTrivialCarDim in ntriv. simpl in ntriv.
  do 3 (rewrite inj_Q_nneg in ntriv).
  apply Qmult_le_r;[| lra].
  apply Qinv_lt_0_compat; lra.
Qed.

(*exact same proof as [βPlusMinusBack] above.*)
Lemma βPlusMinusFront : 
'(polarTheta βMinusFront) ≤ cast CR IR (polarTheta βPlusFront).
Proof using firstQuadW ntriv ntrivStrict. 
  unfold cast, Cart_CR_IR.
  apply CR_leEq_as_IR.
  apply polarFirstQuadMonotone; simpl;
  autounfold with QMC; [tauto| tauto|].
  unfold nonTrivialCarDim in ntriv. simpl in ntriv.
  do 3 (rewrite inj_Q_nneg in ntriv).
  apply Qmult_le_r;[| lra].
  apply Qinv_lt_0_compat; lra.
Qed.


Definition leftBoundWriggle1 : IR := 
  (X (minxy (confineRect1 0))).
Definition leftBoundWriggle2 : IR := 
  (X (minxy (confineRect2 (2 * 'α * 'd)))).

Definition leftBound : IR :=
(min leftBoundWriggle1 leftBoundWriggle2).

(** derive [firstQuadW] from this.*)
Hypothesis maxNeededTurn 
  : (0 : ℝ) ≤ 2 * ' α * ' d ≤ (' polarTheta βPlusFront).

Lemma leftBoundWriggle1Correct: 
isBoundLeftWriggle1 leftBoundWriggle1.
Proof using dNN firstQuadW ntriv turnCentreOut αPos.   
  intros θ Hb. unfold leftBoundWriggle1.
  eapply confineRect1LeftMonotoneRight;
      [reflexivity| |eapply firstQuadW1; eauto].
  split;[reflexivity|].
  rewrite PiBy2DesugarIR. apply PiBy2Ge0.
Qed.

Lemma leftBoundWriggle2Correct: 
isBoundLeftWriggle2 leftBoundWriggle2.
Proof using dNN firstQuadW lengthFrontGreater maxNeededTurn ntriv 
      ntrivStrict turnCentreOut αPos. 
  intros θ Hb. unfold leftBoundWriggle2.
  simpl.
  apply (@order_preserving _ _ _ _ _ _ _ _).
  apply flip_le_negate.
  apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  rewrite CosMinusSwap.
  setoid_rewrite CosMinusSwap at 2.
  apply Cos_resp_leEq.
  - apply flip_le_minus_l.
    rewrite negate_involutive.
    setoid_rewrite plus_0_l.
    eapply transitivity;[|
      apply FrontLeBack].
    apply maxNeededTurn.

  - rewrite (divideBy2 Pi).
    apply plus_le_compat;
        [apply firstQuadβPlusBack|].
    rewrite PiBy2DesugarIR.
    apply flip_le_negate.
    rewrite negate_involutive.
    eapply transitivity;[
        apply MinusPiBy2Le0|].
        destruct Hb.
    eapply transitivity;[|apply H].
    apply adNN; eauto.

  - apply (@order_preserving _ _ _ _ _ _ _ _).
    apply flip_le_negate.
    tauto.
Qed.

Lemma leftBoundCorrect: 
isBoundLeftWriggle leftBound.
Proof.
  unfold leftBound.
  split; intros θ H.
  - eapply transitivity;[apply Min_leEq_lft|].
    apply leftBoundWriggle1Correct. assumption.
  - eapply transitivity;[apply Min_leEq_rht|].
    apply leftBoundWriggle2Correct. assumption.
Qed.

Require Import geometry2D.

Definition isBoundRightWriggle1 (maxx: IR) :=
forall θ:IR,
(0 ≤ θ ≤ 'α * 'd
 → X (maxxy (confineRect1 θ)) ≤ maxx).
 
Definition isBoundRightWriggle2 (maxx: IR) :=
forall θ:IR,
 ('α * 'd ≤ θ ≤ 2 * 'α * 'd
   →  X (maxxy (confineRect2 θ)) ≤ maxx).

Definition isBoundRight (maxx: IR) :=
isBoundRightWriggle1 maxx /\ isBoundRightWriggle2 maxx.
(** As shown below in [rightBoundCorrect],
The extrema is achieved at the end of the first move. *)

Definition rightBound : IR :=
  (X (maxxy (confineRect1 ('α * 'd)))).

(*the equations for the the motion of the front RHS
corner of the car for the 1st and the 2nd move must agree
at the transition time.*)
Lemma transitionMaxX : 
trr * (2 * Sin (' α * ' d)) +
' (| βMinusFront |) 
* Cos (' α * ' d + ' polarTheta βMinusFront)
= ' (| βPlusFront |) *
Cos (' α * ' d - ' polarTheta βPlusFront).
Proof using.
  fold CosClassIR.
  fold (@cos IR _).
  fold SinClassIR.
  fold (@sin IR _).
  rewrite <- unitVDot.
  rewrite <- unitVDot2.
  do 2 rewrite multDotRight.
  pose proof CartToPolarCorrect as H.
  simpl in H. unfold norm, NormCart2DQ in H.
  rewrite <- H.
  rewrite <- H.
  unfold inprod, InProductCart2D.
  simpl.
  (* the above part was copied from [LeftBoundEqSimpl]*)
  unfold trr.
  rewrite preserves_minus.
  rewrite preserves_plus.
  IRring.
Qed.

(**actually only half of [maxNeededTurn] is needed.
*)
Lemma rightBoundCorrectWriggle1 
  : isBoundRightWriggle1 rightBound.
Proof using firstQuadW maxNeededTurn ntriv ntrivStrict turnCentreOut.
  unfold  rightBound.
  intros ? Hb. simpl.
  do 2 rewrite plus_0_l.
  apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  rewrite CosMinusSwap.
  setoid_rewrite CosMinusSwap at 2.
  apply Cos_resp_leEq.
  - apply flip_le_minus_l.
    rewrite negate_involutive.
    setoid_rewrite plus_0_l.
    eapply transitivity;[|
      apply maxNeededTurn].
    rewrite <- (@simple_associativity _ _ plus _ _).
    apply rings.RingLeProp2.
    destruct Hb. eapply transitivity; eauto.
  - rewrite (divideBy2 Pi).
    apply plus_le_compat;
      [apply firstQuadβPlusFront|].
    rewrite PiBy2DesugarIR.
    apply flip_le_negate.
    rewrite negate_involutive.
    eapply transitivity;[
      apply MinusPiBy2Le0|].
    apply Hb.
  - apply (@order_preserving _ _ _ _ _ _ _ _).
    apply flip_le_negate.
    tauto.
Qed.

Lemma rightBoundCorrectWriggle2
  : isBoundRightWriggle2 rightBound.
Proof using dNN firstQuadW maxNeededTurn ntriv ntrivStrict turnCentreOut αPos.
  unfold  rightBound.
  intros ? Hb. simpl.
  rewrite plus_0_l.
  rewrite <- transitionMaxX.
  apply (@order_preserving _ _ _ _ _ _ _ _).
  apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  apply Cos_resp_leEq.
  - apply plus_resp_nonneg;[|apply firstQuadβMinusFront].
    apply adNN; auto.
  - rewrite (divideBy2 Pi).
    apply plus_le_compat;[|apply firstQuadβMinusFront].
    eapply transitivity;[apply Hb|]. tauto.
  - apply plus_le_compat;[tauto| reflexivity].
Qed.

Lemma rightBoundCorrect 
  : isBoundRight rightBound.
Proof using dNN firstQuadW maxNeededTurn ntriv ntrivStrict turnCentreOut αPos.
  split;[apply rightBoundCorrectWriggle1|apply rightBoundCorrectWriggle2].
Qed.


Definition isBoundBottomWriggle1 (miny: IR) :=
forall θ:IR,
(0 ≤ θ ≤ 'α * 'd
 → miny ≤ Y (minxy (confineRect1 θ))).

Definition isBoundBottomWriggle2 (miny: IR) :=
forall θ:IR,
('α * 'd ≤ θ ≤ 2 * 'α * 'd
   → miny ≤ Y (minxy (confineRect2 θ))).

Definition isBoundBottom (miny: IR) :=
isBoundBottomWriggle1 miny ∧ isBoundBottomWriggle2 miny.

Definition bottomBoundWriggle2 :IR :=
(Y (minxy (confineRect2 (2 * 'α * 'd)))).

Lemma bottomBoundWriggle2Correct : 
  isBoundBottomWriggle2 bottomBoundWriggle2.
Proof using dNN firstQuadW ntriv turnCentreOut αPos. 
  unfold bottomBoundWriggle2.
  intro. simpl.
  intro Hb.
  pose proof (firstQuadW2 _ αPos _ dNN firstQuadW _  Hb)
    as Ht.
  apply (@order_preserving _ _ _ _ _ _ _ _).
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  apply Cos_resp_leEq.
  - apply plus_resp_nonneg;[apply Ht|].
    apply flip_le_minus_r.
    setoid_rewrite plus_0_l.
    apply firstQuadβMinusBack.
  - rewrite (divideBy2 Pi).
    apply plus_le_compat;
      [apply firstQuadW|].
    apply nonneg_minus_compat;[| reflexivity].
    apply firstQuadβMinusBack.
  - apply plus_le_compat;
      [apply Hb| reflexivity]; fail.
Qed.

Require Import MathClasses.interfaces.additional_operations. 

Definition minYCriticalAngle : IR
  := (½ * π - ' polarTheta βPlusBack).

Section MinYCases.


(*
Let increase1 := Y (minxy (confineRect1 ('α * 'd))) - 
(Y (minxy (confineRect1 minYCriticalAngle))).

Let decrease2 := 
Y (minxy (confineRect2 ( 'α * 'd))) - 
(Y (minxy (confineRect2 (2* 'α * 'd)))).

Section MCring.

Lemma multDotLeft : forall (a:IR) (b c : Cart2D IR),
a * (⟨b,c⟩) = ⟨('a) * b, c⟩.
Proof using.
  intros.   unfold inprod, InProductCart2D.
  simpl. IRring.
Qed.  

  Add Ring tempRingIR : (stdlib_ring_theory IR).

Lemma Increase1LeDecrease:
  increase1 ≤ decrease2.
Proof.
  subst increase1 decrease2.
  rewrite (proj1 (confineRectCorrect _)).
  rewrite (proj2 (confineRectCorrect _)).
  rewrite (proj2 (confineRectCorrect _)).
  simpl.
  rewrite <-trComplicated.
  replace (½ * π - ' polarTheta βPlusBack) with 
    minYCriticalAngle;[| reflexivity].
  rewrite plus_negate_r.
  rewrite Cos_zero.
  setoid_rewrite mult_1_r.
  simpl.
  rewrite <- (@simple_associativity _ _ mult _ _ _ _).
  rewrite unitVDoubleAsCos.
  rewrite nat_pow.nat_pow_2.
  unfold inprod, InProductCart2D. simpl.
  fold trr.
  match goal with
  [|- ?l ≤ _] =>
  ring_simplify l
  end.
  ring_simplify (trr * (1 - 2 * cos (' α * ' d)) +
  ((trr - ' width cd) * cos (' α * ' d) + - ' lengthBack cd * sin (' α * ' d))).
  setoid_rewrite (@commutativity _ _ _ plus _ _) at 10.
  rewrite <- flip_le_minus_l.
  match goal with
  [|- ?l ≤ _] =>
  ring_simplify l
  end.
  rewrite  negate_swap_l.
  apply flip_le_negate.
  rewrite plus_mult_distr_l.
  rewrite mult_1_r.
  rewrite <- (@simple_associativity _ _ plus _ _).
  apply (@order_preserving _ _ _ _ _ _ _ _ _).
  apply flip_le_negate.
  rewrite negate_involutive.
  rewrite <- negate_mult_distr_r.
  rewrite  negate_plus_distr.
  rewrite negate_involutive.
  rewrite <- negate_mult_distr_l.
  rewrite <- negate_swap_l.
  rewrite negate_mult_distr_r.
  rewrite <- negate_swap_r.
  rewrite plus_mult_distr_l.
  rewrite mult_1_r.
  rewrite commutativity.
  remember (cos (' α * ' d)) as c.
  remember (sin (' α * ' d)) as s.
  match goal with
  [|- _ ≤ ?l] =>
    assert (l= trr - ' width cd 
    + 2*c*(trr - ((trr - ' width cd)*c - ( ' lengthBack cd)*s))
    ) as H by ring
  end.
  rewrite H. clear H.
  subst c s.
  assert (
  ((trr - ' width cd) * cos (' α * ' d) - ' lengthBack cd * sin (' α * ' d))
  = 
   ⟨ {|X:=1;Y:=-1|} *  transpose ('βMinusBack) , unitVec (' α * ' d)⟩
  ) as H by
  (unfold inprod, InProductCart2D; simpl;
  rewrite preserves_minus; fold trr; ring).
  rewrite H.
  rewrite CartToPolarCorrect90Minus.
  rewrite (@commutativity _ _ _ (@mult (@Cart2D IR) _) _ _).
  rewrite <- (@simple_associativity _ _  (@mult (@Cart2D IR) _) _ _).
  rewrite <- multDotLeft.
  rewrite (@commutativity _ _ _ (@mult (@Cart2D IR) _) _ _).
  rewrite  unitVDot2.
  (*further simplification may lead to a characterization of 
  the [min] in [bottomBoundCase2] below.*)
Abort.

End  MCring.

*)

Definition bottomBoundWriggle1Case1 :IR :=
(Y (minxy (confineRect1 ('α * 'd)))).

Lemma bottomBoundWriggle1Case1Correct :
('α * 'd ≤ minYCriticalAngle)
-> isBoundBottomWriggle1 bottomBoundWriggle1Case1.
Proof using dNN firstQuadW ntriv turnCentreOut αPos. 
  simpl. intros Hu ?. simpl.
  intro Hb.
  pose proof (firstQuadW1 _ αPos _ dNN firstQuadW _  Hb)
    as Ht.
  unfold bottomBoundWriggle1Case1. simpl.
  apply (@order_preserving _ _ _ _ _ _ _ _).
  apply flip_le_negate.
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  rewrite CosMinusSwap.
  setoid_rewrite CosMinusSwap at 2.
  apply Cos_resp_leEq.
  - apply flip_le_minus_r.
    setoid_rewrite plus_0_l.
    apply Hu.
  - rewrite (divideBy2 Pi).
    apply plus_le_compat;[|].
    + apply nonneg_minus_compat;[|reflexivity].
      apply firstQuadβPlusBack.
    + rewrite PiBy2DesugarIR.
      eapply transitivity;[|apply PiBy2Ge0].
      apply flip_le_negate.
      rewrite negate_involutive.
      setoid_rewrite negate_0.
      apply Ht.
  - apply plus_le_compat;
      [reflexivity|].
    apply flip_le_negate.
    apply Hb.
Qed.

Definition bottomBoundWriggle1Case2 :IR :=
(Y (minxy (confineRect1 minYCriticalAngle))).

Lemma bottomBoundWriggle1Case2Correct: 
(minYCriticalAngle ≤ 'α * 'd )
-> isBoundBottomWriggle1 bottomBoundWriggle1Case2.
Proof using dNN firstQuadW αPos.
  simpl. intros Hu ?. unfold bottomBoundWriggle1Case2.
  simpl.
  intro Hb.
  unfold minYCriticalAngle.
  rewrite plus_negate_r.
  rewrite Cos_zero.
  pose proof (firstQuadW1 _ αPos _ dNN firstQuadW _  Hb)
    as Ht.
  apply (@order_preserving _ _ _ _ _ _ _ _).
  apply flip_le_negate.
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  apply Cos_leEq_One.
Qed.

Definition bottomBoundCase1 : IR :=
  bottomBoundWriggle2.

Definition bottomBoundCase2 : IR :=
  min
    bottomBoundWriggle1Case2
    bottomBoundCase1.

(*the equations for the the motion of the car for the 1st and the 2nd move must agree
at the transition time.*)
Lemma transitionMinY : 
Y (minxy (confineRect2 (' α * ' d)))
= Y (minxy (confineRect1 (' α * ' d))).
Proof using αPos.
  rewrite  (proj2 (confineRectCorrect _)).
  rewrite  (proj1 (confineRectCorrect _)).
  simpl. fold αNZ.
  rewrite <- trComplicated.
  unfold inprod, InProductCart2D.
  simpl.
  IRring.
Qed.



Lemma bottomBoundCase1Correct : 
('α * 'd ≤ minYCriticalAngle)
-> isBoundBottom bottomBoundCase1.
Proof using dNN firstQuadW ntriv turnCentreOut αPos.
  intros Hu.
  split; intro.
- intros Hb. eapply transitivity;
    [|apply bottomBoundWriggle1Case1Correct; trivial; fail].
  unfold bottomBoundCase1.
  rewrite <- transitionMinY.
  apply bottomBoundWriggle2Correct.
  split;[reflexivity|].
  rewrite <- (@simple_associativity _ _ mult _ _ _).
  apply rings.RingLeProp2.
  destruct Hb. eapply transitivity; eauto.
- intros Hb.
  apply bottomBoundWriggle2Correct. auto.
Qed.

Lemma bottomBoundCase2Correct : 
(minYCriticalAngle ≤ 'α * 'd)
-> isBoundBottom bottomBoundCase2.
Proof using dNN firstQuadW ntriv turnCentreOut αPos.
  intros Hu.
  split; intro.
- intros Hb. eapply transitivity;
    [apply Min_leEq_lft|].
  apply bottomBoundWriggle1Case2Correct; trivial.
- intros Hb.
  eapply transitivity;
    [apply Min_leEq_rht|].
  apply bottomBoundWriggle2Correct; auto.
Qed.

End  MinYCases.

(** Even though the extra space needed in the upward direction
 is not at all a concern, some bound, possibly very sloppy,
  is needed because most lemmas
 about space analysis of a sequence of moves are in terms of bounds
 in all 4 directions. *)
Definition isBoundUpWriggle1 (maxy: IR) :=
forall θ:IR,
(0 ≤ θ ≤ 'α * 'd
 → Y (maxxy (confineRect1 θ)) ≤ maxy).
 
Definition isBoundUpWriggle2 (maxy: IR) :=
forall θ:IR,
 ('α * 'd ≤ θ ≤ 2 * 'α * 'd
   →  Y (maxxy (confineRect2 θ)) ≤ maxy).

Definition isBoundUp (maxy: IR) :=
isBoundUpWriggle1 maxy /\ isBoundUpWriggle2 maxy.

Definition upBoundWriggle1 : IR :=
Y (maxxy (confineRect1 ('α * 'd))).

Lemma upBoundWriggle1Correct 
  : isBoundUpWriggle1 upBoundWriggle1.
Proof using dNN firstQuadW maxNeededTurn ntriv ntrivStrict turnCentreOut αPos.
  intros ? Hb. unfold upBoundWriggle1. simpl.
  apply (@order_preserving _ _ _ _ _ _ _ _).
  apply flip_le_negate.
  apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  apply Cos_resp_leEq.
  - apply nonneg_plus_compat; unfold PropHolds;
      [ eapply firstQuadW1; eauto|].
    apply flip_le_minus_l.
    rewrite negate_involutive.
    setoid_rewrite plus_0_l.
    apply firstQuadβMinusFront.
  - rewrite (divideBy2 Pi).
    apply plus_le_compat;
      [ apply adPiBy2; assumption|].
    apply flip_le_minus_l.
    rewrite (@commutativity _ _ _ plus _ _).
    apply RingLeProp1.
    apply firstQuadβMinusFront.
  - apply plus_le_compat; unfold PropHolds;
      [| reflexivity].
    tauto.
Qed.

(**perhaps a sloppy bound, but as mentioned above, the extra space 
used at the upward side is not a concern at all.
It appears that in some cases, this bound is tight, and the 
highest point of the circle is achieved.
*)
Definition upBoundWriggle2 : IR :=
(trr * (1 - 2 * Cos (' α * ' d)) +' (| βPlusFront |)).

Lemma upBoundWriggle2Correct
  : isBoundUpWriggle2 upBoundWriggle2.
Proof using.
  intros ? Hb. unfold upBoundWriggle2. simpl.
  apply (@order_preserving _ _ _ _ _ _ _ _).
  setoid_rewrite <- (mult_1_r (' (| βPlusFront |))) at 3.
  apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
  apply Cos_leEq_One.
Qed.

(**perhaps a sloppy bound, but as mentioned above, the extra space 
used at the upward side is not a concern at all. *)
Definition upBound  :IR :=
max upBoundWriggle1 upBoundWriggle2.


Lemma upBoundCorrect 
  : isBoundUp upBound.
Proof using dNN firstQuadW maxNeededTurn ntriv ntrivStrict turnCentreOut αPos.
  unfold upBound.
  split; intros θ H.
  - eapply transitivity;[|apply lft_leEq_Max].
    apply upBoundWriggle1Correct. assumption.
  - eapply transitivity;[|apply rht_leEq_Max].
    apply upBoundWriggle2Correct. assumption.
Qed.

Definition WriggleConfineRectFirstQ (bottomBound : IR): Line2D IR :=
{| minxy := {| X := leftBound ; Y:= bottomBound|};
  maxxy := {| X := rightBound ; Y:= upBound |}
|}.



  Local Opaque confineRect1.
  Local Opaque confineRect2.

Lemma WriggleConfineRectFirstQCase1Correct :
('α * 'd ≤ minYCriticalAngle)
→ carConfinedDuringAMs ('cd) 
    (WriggleConfineRectFirstQ bottomBoundCase1)
    SWriggle
    (0 : Rigid2DState ℝ).
Proof using dNN firstQuadW lengthFrontGreater maxNeededTurn ntriv 
ntrivStrict turnCentreOut.
  intro Hcase1.
  apply WriggleFirstQSpace2; try assumption; [].
  intro.
  rewrite <- (proj1 (confineRectCorrect _)).
  rewrite <- (proj2 (confineRectCorrect _)).
  split; intro Hb; split; split; simpl; revert Hb; revert θ;
  try apply leftBoundCorrect;
  try apply rightBoundCorrect; 
  try apply upBoundCorrect; 
  try apply bottomBoundCase1Correct; 
  auto.
Qed.

Lemma WriggleConfineRectFirstQCase2Correct :
(minYCriticalAngle ≤ 'α * 'd)
→ carConfinedDuringAMs ('cd) 
    (WriggleConfineRectFirstQ bottomBoundCase2)
    SWriggle
    (0 : Rigid2DState ℝ).
Proof using dNN firstQuadW lengthFrontGreater maxNeededTurn ntriv 
ntrivStrict turnCentreOut.
  intro Hcase1.
  apply WriggleFirstQSpace2; try assumption; [].
  intro.
  rewrite <- (proj1 (confineRectCorrect _)).
  rewrite <- (proj2 (confineRectCorrect _)).
  split; intro Hb; split; split; simpl; revert Hb; revert θ;
  try apply leftBoundCorrect;
  try apply rightBoundCorrect; 
  try apply upBoundCorrect; 
  try apply bottomBoundCase2Correct; 
  auto.
Qed.

  Local Transparent confineRect1.
  Local Transparent confineRect2.

Variable d':IR.
Hypothesis d'NN : 0 ≤ d'.

Let sidewaysMove : list DAtomicMove 
  := SidewaysAux ('α) αNZ ('d) (d').

Definition sidewaysFirstQ bottomBound :=
(sidewaysRect  ('α) ('d) (d') (WriggleConfineRectFirstQ bottomBound) 0).

Lemma SidewaysConfineRectFirstQCase1Correct :
('α * 'd ≤ minYCriticalAngle)
→ carConfinedDuringAMs ('cd) 
    (sidewaysFirstQ bottomBoundCase1)
    sidewaysMove
    (0 : Rigid2DState ℝ).
Proof using dNN firstQuadW lengthFrontGreater maxNeededTurn
     ntriv ntrivStrict turnCentreOut αNZ.
  intro Hcase1. unfold sidewaysFirstQ.
  apply SidewaysAuxSpace.
  apply WriggleConfineRectFirstQCase1Correct.
  assumption.
Qed.

Lemma SidewaysConfineRectFirstQCase2Correct :
(minYCriticalAngle ≤ 'α * 'd)
→ carConfinedDuringAMs ('cd) 
    (sidewaysFirstQ bottomBoundCase2)
    sidewaysMove
    (0 : Rigid2DState ℝ).
Proof using dNN firstQuadW lengthFrontGreater 
    maxNeededTurn ntriv ntrivStrict turnCentreOut αNZ.
  intro Hcase1. unfold sidewaysFirstQ.
  apply SidewaysAuxSpace.
  apply WriggleConfineRectFirstQCase2Correct.
  assumption.
Qed.


(**can some reasonable assumption replace [min] by either of its arguments?*)
Lemma LeftBoundSimpl : leftBound = 
min 
  (- ' lengthBack cd) (**initial state , i.e. start of the first move*)
  ( 2 * 'tr   * Sin (' α * ' d)
     -⟨ '{| X := lengthBack cd; Y := tr + width cd |},unitVec (2 * ' α * ' d)⟩) .
     (**end of the second move*)
Proof using αPos.
  match goal with
  [|- _= ?r] => remember r as rr
  end.
  unfold leftBound, leftBoundWriggle1, leftBoundWriggle2.
  rewrite  (proj2 (confineRectCorrect _)).
  rewrite  (proj1 (confineRectCorrect _)).
  simpl. fold αNZ.
  rewrite <- trComplicated.
  subst rr.
  unfold inprod, InProductCart2D.
  simpl.
  fold CosClassIR.
  fold (@cos IR _).
  rewrite Cos_zero.
  rewrite Sin_zero.
  unfold trr.
  rewrite preserves_plus.
  apply Min_wd_unfolded; split; simpl; IRring.
Qed.

(** achieved at end of 1st move *)
Lemma RightBoundSimpl : rightBound = 
⟨ ' {| X :=  lengthFront cd; Y :=  tr +  width cd |} , unitVec (' α * ' d)⟩.
Proof using αPos.
  match goal with
  [|- _= ?r] => remember r as rr
  end.
  unfold rightBound.
  rewrite  (proj1 (confineRectCorrect _)).
  simpl. fold αNZ.
  rewrite <- trComplicated.
  subst rr. 
  unfold inprod, InProductCart2D.
  simpl.
  rewrite preserves_plus. 
  reflexivity.
Qed.

(** achieved at end of 2nd move *)
Lemma BottomBoundCase1Simpl : bottomBoundCase1 = 
' tr * (1 - 2 * cos (' α * ' d)) +
(⟨ '{| X :=  tr -  width cd; Y := - lengthBack cd |}, unitVec (2 * ' α * ' d) ⟩).
Proof using αPos.
  match goal with
  [|- _= ?r] => remember r as rr
  end.
  unfold bottomBoundCase1, bottomBoundWriggle2.
  rewrite  (proj2 (confineRectCorrect _)).
  simpl.  fold αNZ.
  rewrite <- trComplicated.
  subst rr. 
  unfold inprod, InProductCart2D.
  simpl.
  rewrite preserves_plus.
  do 2 rewrite preserves_negate.
  reflexivity.
Qed.

(**can some reasonable assumption replace [min] by either of its arguments?*)
Lemma BottomBoundCase2Simpl : bottomBoundCase2 = 
min (trr - ' (| βPlusBack |)) (** extrema inside the 1st move*)
    bottomBoundCase1. (** end of 2nd move *)
Proof using αPos.
  unfold bottomBoundCase2, bottomBoundWriggle1Case2.
  apply Min_wd_unfolded; split;[| reflexivity].
  simpl.
  rewrite plus_negate_r.
  rewrite Cos_zero.
  IRring.
Qed.

(**subtract the initially needed space*)
Definition leftExtraSpace :IR :=
-(leftBound - (- 'lengthBack cd)).

Definition rightExtraSpace :IR :=
(rightBound - 'lengthFront cd).

Definition extraSpaceX :IR :=
leftExtraSpace + rightExtraSpace.

Lemma rightExtraSpaceSimpl : rightExtraSpace =
⟨ ' {| X := lengthFront cd; Y := tr + width cd |}, unitVec (' α * ' d) ⟩ -
' lengthFront cd .
Proof using αPos.
  unfold rightExtraSpace.
  rewrite  RightBoundSimpl.
  reflexivity.
Qed.



Lemma leftExtraSpaceSimpl1 : leftExtraSpace =
max 0
  (⟨' {| X := lengthBack cd; Y := tr + width cd |}, unitVec (2 * ' α * ' d)⟩ 
     - ' lengthBack cd 
     - 2 * ' tr * Sin (' α * ' d)).
Proof using αPos.
  hideRight.
  unfold leftExtraSpace.
  rewrite <- negate_swap_r.
  rewrite <- negate_plus_distr.
  rewrite  LeftBoundSimpl.
  rewrite <- Min_plusl.
  rewrite plus_negate_r.
  rewrite negateMinAsMax.
  subst. apply Max_wd_unfolded; IRring.
Qed.

Definition leftExtraSpaceTerm := 
⟨'{|X := tr + width cd; Y:= -lengthBack cd|}, unitVec (' α * ' d)⟩.

Lemma leftExtraSpaceSimpl2 : leftExtraSpace =
max 0 (2 * sin (' α * ' d) * (leftExtraSpaceTerm - 'tr)).
Proof using αPos.
  unfold leftExtraSpaceTerm.
  hideRight. rewrite leftExtraSpaceSimpl1.
  pose proof (unitVDouble (' α * ' d)) as Hh.
  rewrite  (@simple_associativity _ _ mult _ _ _) in Hh.
  rewrite Hh. clear Hh.
  subst.  apply Max_wd_unfolded; [IRring|].
  simpl.
  rewrite nat_pow.nat_pow_2.
  unfold inprod, InProductCart2D. simpl.
  rewrite preserves_negate.
  IRring.
Qed.

Lemma leftExtraSpaceTermSimpl : leftExtraSpaceTerm =
  (' (| βPlusBack |) * cos (' α * ' d + (½ * π - ' polarTheta βPlusBack))).
Proof using.
  unfold leftExtraSpaceTerm.
  hideRight. simpl.
  subst.
  fold CosClassIR.
  fold (@cos IR _).
  rewrite <- unitVDot2.
  rewrite multDotRight.
  pose proof CartToPolarCorrect90Minus as Hr.
  unfold norm, NormCart2DQ in Hr.
  rewrite <- Hr.
  unfold inprod, InProductCart2D. simpl.
  rewrite preserves_plus.
  rewrite preserves_negate.
  IRring.
Qed.

(**from the above representation, it is clear that at small angles,
  [leftExtraSpaceTerm] is closer to [| βPlusBack |], which is slight larger than
  [tr+width cd], and hence larger than [tr]. Hence the second argument
  of [max] in [leftExtraSpaceSimpl2 ]will be positive.
  
  On the other hand, when [' α * ' d] is large, [cos] will be closer to [0],
  and [max] will be equal to the left argument, i.e. minima achieved at
  the initial position.
  Note that [(½ * π - ' polarTheta βPlusBack)] typically a small angle.
  See [Mazda3βPlusBack] below.
  *)

Let cyyQ : Q :=  ((width cd)^2 + (lengthBack cd)^2 + 2* tr* (width cd))%mc.

Let cyy : CR :=  √cyyQ.


Lemma cyyQNonneg: (0  ≤ cyyQ).
Proof using ntriv ntrivStrict turnCentreOut. 
  destruct ntrivStrict.
  unfold nonTrivialCarDim in ntriv.
  simpl in ntriv.
  do 3 rewrite inj_Q_nneg in ntriv.
  destruct ntriv as [H11 H12]. destruct H12.
  unfold cyyQ.
  rewrite nat_pow.nat_pow_2.
  rewrite nat_pow.nat_pow_2.
  autounfold with QMC.
  pose proof (Qmult_le_0_compat _ _ H2 H2).
  pose proof (Qmult_le_0_compat _ _ H1 H1).
  assert (0 <= tr)%Q as X by lra.
  pose proof (Qmult_le_0_compat _ _  X H1).
  lra.
Qed.
  

Lemma cyyCorrect: 
√ ('(tr * tr) + cyy * cyy) = (| βPlusBack | : CR).
Proof using ntriv ntrivStrict turnCentreOut. 
  simpl. unfold cyy. unfold CanonicalNotations.norm, NormSpace_instance_Cart2D.
  unfold sqrtFun, rational_sqrt_SqrtFun_instance, CRsqrt_SqrtFun_instance.
  rewrite <- CRsqrt_Qsqrt.
  rewrite <- CRsqrt_Qsqrt.
  apply ProperCRsqrt.
  let tac := (apply CRle_Qle;apply cyyQNonneg) in
    rewrite <- CRsqrt_mult;[rewrite CRsqrt_ofsqr_nonneg;[|tac]| tac|tac].
  fold (cast Q CR).
  rewrite <- (@preserves_plus Q CR _ _ _ _ _ _ _ _ _ _ _ _ ).
  apply sm_proper.
  unfold cyyQ.
  rewrite nat_pow.nat_pow_2.
  rewrite nat_pow.nat_pow_2.
  autounfold with QMC.
  simpl.
  autounfold with QMC.
  ring.
Qed.

Hypothesis widthLt: (0 < width cd)%Q.

Definition leftCriticalAngle :IR :=
' arctan (cyy * ' (/ tr)) - (½ * π - ' polarTheta βPlusBack).

Lemma leftCriticalAngleVsMiny :
leftCriticalAngle = ' arctan (cyy * ' (/ tr)) - minYCriticalAngle.
Proof using.
  reflexivity.
Qed.

Lemma nonTrivialExtraSpaceIf :
' α * ' d ≤ leftCriticalAngle
→ 'tr ≤ leftExtraSpaceTerm.
Proof using dNN ntriv ntrivStrict turnCentreOut αPos widthLt.
  unfold leftCriticalAngle.
  intro. rewrite leftExtraSpaceTermSimpl.
  eapply transitivity.
  - apply eq_le. 
    apply cos_o_arctan_east2Q with (cy:=cyy).
    lra.
  - unfold leftExtraSpaceTerm. rewrite cyyCorrect.
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
    apply Cos_resp_leEq.
    + apply plus_resp_nonneg; [apply adNN; auto|].
      apply flip_le_minus_r.
      setoid_rewrite plus_0_l.
      apply firstQuadβPlusBack.
    + rewrite arctan_correct_CR.
      rewrite (divideBy2 Pi).
      eapply transitivity.
      * apply less_leEq. apply ArcTan_range.
      * rewrite PiBy2DesugarIR. apply RingLeProp1.
        apply PiBy2Ge0.
    + apply flip_le_minus_r. assumption.
Qed.

Lemma trivialExtraSpaceIf :
leftCriticalAngle ≤ ' α * ' d
→ leftExtraSpaceTerm ≤ 'tr.
Proof using dNN firstQuadW ntriv ntrivStrict turnCentreOut widthLt αPos.
  unfold leftCriticalAngle.
  intro.  rewrite leftExtraSpaceTermSimpl.
  eapply transitivity.
  Focus 2.
  - apply eq_le. symmetry. 
    apply cos_o_arctan_east2Q with (cy:=cyy). lra.
  - rewrite cyyCorrect.
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
    apply Cos_resp_leEq.
    + rewrite arctan_correct_CR.
      apply ArcTan_nonneg.
      rewrite <- CRasIR0.
      apply CR_leEq_as_IR.
      apply nonneg_mult_compat; unfold PropHolds.
      * unfold cyy. rewrite <- CRsqrt_Qsqrt.
        apply CRsqrt_nonneg.
        apply preserves_nonneg.
        unfold PropHolds.
        apply cyyQNonneg.
      * apply preserves_nonneg.
        unfold PropHolds.
        apply Qinv_le_0_compat.
        unfold nonTrivialCarDim in ntriv.
        simpl in ntriv.
        do 3 rewrite inj_Q_nneg in ntriv.
        lra.
    + rewrite (divideBy2 Pi).
      apply plus_le_compat;[apply adPiBy2; assumption|].
      apply  flip_le_minus_r.
      rewrite negate_involutive.
      rewrite (@commutativity _ _ _ plus _ _).
      apply RingLeProp1.
      apply firstQuadβPlusBack.

    + apply flip_le_minus_l. assumption.
Qed.

Definition leftCriticalAngleCR :CR :=
 arctan (cyy * ' (/ tr)) - (½ * π - polarTheta βPlusBack).


Lemma leftCriticalAngleCRCorrect :
'leftCriticalAngleCR = leftCriticalAngle.
Proof using.
  unfold leftCriticalAngleCR, leftCriticalAngle.
  rewrite CR_minus_asIR.
  rewrite CR_minus_asIR.
  rewrite <- PiBy2IRCR.
  reflexivity.
Qed.

(** for Mazda 3, it is between 23 and 24 degrees *)
Lemma Mazda3LeftCriticalAngle:
thisCarHasSameGeometryAs ('Mazda3Sedan2014sGT)
-> ('(Qmake 23 180) * π ) < leftCriticalAngleCR < ('(Qmake 24 180) * π ).
Proof using.
  intro H. destruct H as [Hl Hr].
  unfold leftCriticalAngleCR.
  unfold cyy, cyyQ, βPlusBack.
  subst.
  rewrite Hr. clear Hr.
  unfold lt, CRlt.
  split; exists 7%nat;
  simpl; vm_compute; reflexivity.
Qed.

(** lets consider the two subcomponents of the above angle *)
Lemma Mazda3LeftCriticalAngle1:
thisCarHasSameGeometryAs ('Mazda3Sedan2014sGT)
-> ('(Qmake 33 180) * π ) < arctan (cyy * ' (/ tr)) < ('(Qmake 34 180) * π ).
Proof using.
  intro H. destruct H as [Hl Hr].
  unfold leftCriticalAngleCR.
  unfold cyy, cyyQ.
  subst.
  rewrite Hr. clear Hr.
  unfold lt, CRlt.
  split; exists 10%nat;
  simpl; vm_compute; reflexivity.
Qed.

Lemma Mazda3βPlusBack:
thisCarHasSameGeometryAs ('Mazda3Sedan2014sGT)
-> ('(Qmake 79 180) * π ) < polarTheta βPlusBack < ('(Qmake 80 180) * π ).
Proof using.
  intro H. destruct H as [Hl Hr].
  unfold leftCriticalAngleCR.
  unfold βPlusBack.
  subst.
  rewrite Hr. clear Hr.
  unfold lt, CRlt.
  split; exists 10%nat;
  simpl; vm_compute; reflexivity.
Qed.

Definition CRPiInv : CR := CRinvT CRpi (inr CRpi_pos).


Definition approximateAngleAsDegrees (a:CR) : Z :=
 R2ZApprox (a*CRPiInv* ('180%positive)) (QposMake 1 100).


(** 
does not compute:

Eval vm_compute in  
  (approximateAngleAsDegrees
    (polarTheta 
      (CornerAngles.βPlusFront 
        ('carDim Mazda3Sedan2014sGT)
        (' minTR Mazda3Sedan2014sGT)
         ))).

Perhaps this is the root cause, which does not compute either.
Eval vm_compute in  
 (approximate (CRPiInv) (QposMake 1 1)).

Is there a fast implementation of reciprocal for CR?
It does not even look at the positivity proof, so it is 
perhaps wasting time computing already available info.

Perhaps switch to AR? The reciprocal function there (ARinv) also does not
seem to look at the positivity proof.
*)

Lemma Mazda3βPlusFront:
thisCarHasSameGeometryAs ('Mazda3Sedan2014sGT)
-> ('(Qmake 51 180) * π ) < polarTheta βPlusFront < ('(Qmake 52 180) * π ).
Proof using.
  intro H. destruct H as [Hl Hr].
  unfold leftCriticalAngleCR.
  unfold βPlusFront.
  subst.
  rewrite Hr. clear Hr.
  unfold lt, CRlt.
  split; exists 10%nat;
  simpl; vm_compute; reflexivity.
Qed.

Section LeftNontrivialCase.

(*Move *)
Lemma PiBy2LePiMC : ½ * Pi [<=] Pi.
Proof using.
  rewrite PiBy2DesugarIR. apply less_leEq. apply HalfPi_less_Pi.
Qed.

(** It almost-suffices to just consider this case, which is defined by
  [' α * ' d ≤ leftCriticalAngle].
We know that it suffices to pick ['d] such that [2*' α * ' d ≤ polarTheta βPlusFront].
The latter is about 51 degrees. [' α * ' d] is half of that, so we loose nothing if
we consider the case when [' α * ' d ≤ 26].
[leftCriticalAngle] is around 24 degrees for Mazda3. 
Therefore, ensuring [' α * ' d ≤ 24] may be only slightly suboptimal.
Note that we get to control [d].
Also, as the available space gets smaller, other constraints will anyways force us
to choose a smaller positive value of [d], reaching 0 in the limit.

  In this case, the [max] in
  [leftExtraSpaceSimpl2] above can be simplified to its RHS.
*)

Lemma leftExtraSpaceSimplCase1 :
' α * ' d ≤ leftCriticalAngle
→ leftExtraSpace =
    (2 * sin (' α * ' d) * (leftExtraSpaceTerm - 'tr)).
Proof using dNN firstQuadW ntriv ntrivStrict turnCentreOut widthLt αPos. 
  intro.
  rewrite leftExtraSpaceSimpl2.
  apply leEq_imp_Max_is_rht.
  rewrite <- (@simple_associativity _ _ mult _ _ ).
  apply RingLeProp3.
  apply nonneg_mult_compat; unfold PropHolds.
  - apply Sin_nonneg;[apply adNN; assumption|].
    eapply transitivity;[apply adPiBy2; assumption|].
    apply PiBy2LePiMC.
  - apply flip_le_minus_r. rewrite plus_0_l.
    apply nonTrivialExtraSpaceIf. assumption.
Qed.

Definition extraSpaceXCase1 :IR :=
(2 * sin (' α * ' d) * (leftExtraSpaceTerm - 'tr)) + rightExtraSpace.

Lemma extraSpaceXCase1Correct :
' α * ' d ≤ leftCriticalAngle
→ extraSpaceXCase1 = extraSpaceX.
Proof using dNN firstQuadW ntriv ntrivStrict turnCentreOut widthLt αPos.
  unfold extraSpaceXCase1, extraSpaceX.
  intro H. rewrite leftExtraSpaceSimplCase1;[| assumption].
  reflexivity.
Qed.


(**Lets try to further simplify [extraSpaceXCase1].
Below, it is expressed entiredly as a function of [(' α * ' d)].
More specifically, only in terms or [sin (' α * ' d)] and [cos (' α * ' d)]
[cos (' α * ' d)] can be expressed as [sin (' α * ' d)], and hence, we
can get rid of trigonometry altogether in the upcoming optimization needed
to pick the value of [d], given the amount of extra space available.
[(' α * ' d)] is between 0 and quarter Pi.
So  [sin (' α * ' d)] is between 0 and 1/sqrt 2.
*)

Lemma extraSpaceXCase1Simpl2 :
  let θ :IR := (' α * ' d) in 
  extraSpaceXCase1 = 
  2 * (trr + ' width cd) * sin θ * cos θ 
  - 2 * ' lengthBack cd * (sin θ) ^2
  + (' width cd - trr) * sin θ
  + ' lengthFront cd * cos θ
  - ' lengthFront cd.
Proof using αPos. 
  simpl.
  hideRight.
  unfold extraSpaceXCase1.
  rewrite rightExtraSpaceSimpl.
  unfold leftExtraSpaceTerm.
  unfold inprod, InProductCart2D.
  simpl. rewrite preserves_plus.
  rewrite preserves_negate.
  fold trr. subst.
  rewrite nat_pow.nat_pow_2.
  IRring.
Qed.
End LeftNontrivialCase.

End FirstQuadWriggleQ.