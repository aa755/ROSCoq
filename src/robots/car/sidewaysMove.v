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

Definition unitVecT `{SinClass R} `{CosClass R} (t:R) := transpose (unitVec t).

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

(*  Lemma Wriggleθ2  
  `{CarExecutesAtomicMovesDuring (Wriggle tc distance) tstart tend p} :
  {theta acs} tend =  {theta acs} tstart + 2 * tc * distance.
  Proof.
    
    invertAtomicMoves. rename Hf into amscrl.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl. rewrite amscl in amscrl.
    rewrite amscrl.
    autounfold with IRMC. ring.    
  Qed.
*)

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
  Lemma SidewaysAuxState : forall init,
  stateAfterAtomicMoves SidewaysAux init
  = {|pos2D := pos2D init 
      + '(d') * unitVec ((θ2D init) + 2 * α * d);
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
  Lemma SidewaysAuxSpace :
  ∀  (cd : CarDimensions ℝ)
  (init : Rigid2DState ℝ)
  (confineRect: Line2D IR), 
  let rectR := confineRect 
    + '('(d') * unitVec ((θ2D init) + 2 * α * d)) in
  let cmr := boundingUnion confineRect rectR in
carConfinedDuringAMs cd confineRect SWriggle init
-> carConfinedDuringAMs cd cmr SidewaysAux init.
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
    simpl. rewrite mult_0_l, plus_0_r.
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

(*Move*)
Lemma inBetweenExpand `{PreOrder A r} : forall a b c a' c':A,
(r a b /\ r b c) 
-> (r a' a /\ r c c')
-> (r a' b /\ r b c').
Proof using.
  intros. repnd.
  split; eapply transitivity; eauto.
Qed.

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


Local Notation  αNZ := ((pos_ap_zero _ _ αPos): α[#]0).
Local Notation init  := (0:Rigid2DState IR).

Local Notation SWriggle := (Wriggle α αNZ d).

Local Notation tr := ((@f_rcpcl ℝ α (pos_ap_zero ℝ α αPos))).
(*Move *)
Lemma and_iff_compat_lr: 
  ∀ A B C D: Prop, ((A ↔ D)∧ (B ↔ C)) → (A ∧ B ↔ D ∧ C).
Proof using.
  intros. tauto.
Qed.
Lemma iff_under_imp: 
  ∀ A B C: Prop, (A → (B ↔ C)) → ((A → B) ↔ (A → C)).
Proof using.
  intros. tauto.
Qed.
Lemma andWeakenL : forall (A B C :Prop),
    (A -> B) -> (A /\ C) -> (B /\ C).
Proof using.
    tauto.
Qed.
Lemma iff_under_imp2: 
  ∀ A B C: Prop, ((B ↔ C)) → ((A → B) ↔ (A → C)).
Proof using.
  intros. tauto.
Qed.
Lemma po_properL:
  ∀ (A : CProp) (Ae : Equiv A) (Ale : Le A) (a:A),
  PartialOrder Ale → Equivalence (@equiv A _) → Proper (equiv ==> iff)
    (fun x=> le x a).
Proof using.
  intros ? ? ? ? ? ? ? ? ?. apply po_proper; auto.
Qed.



(*apply mult_resp_nonneg; auto 2 with CoRN.*)

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

Lemma WriggleFirstQSpace2 :  ∀  (confineRect: Line2D IR),
(∀ θ:IR,
(0 ≤ θ ≤ α * d
 → {|
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
                 unitVec θ ⟩) + tr |} |} ⊆ confineRect)
∧ (α * d ≤ θ ≤ 2 * α * d
   → ' (' tr * {| X := 2 * sin (α * d); 
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
                   |}
     ⊆ confineRect))
  <->
  carConfinedDuringAMs cd confineRect SWriggle init.
Proof using All.
  intros ?. rewrite <- WriggleFirstQSpace.
  apply iff_under_forall.
  intro θ.
  remember (f_rcpcl α (pos_ap_zero ℝ α αPos)) as trr.
  clear Heqtrr.
  apply and_iff_compat_lr.
  eapply andWeakenL.
  exact (iff_under_imp2 _ _ _).
  apply and_comm.
  eapply andWeakenL.
  exact (iff_under_imp2 _ _ _).
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

(*Move*)
Global Instance CastCarDim `{Cast A B} 
  : Cast (CarDimensions A) (CarDimensions B) :=
fun a =>  Build_CarDimensions 
            ('lengthFront a)
            ('lengthBack a) 
            ('width a).

Section FirstQuadWriggleQ.

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
  *)
Variable α : Q.
Hypothesis αPos : ((0:IR)[<]'α).
Variable d : Q.
Variable cd : CarDimensions Q.
Hypothesis ntriv : nonTrivialCarDim (' cd).
Hypothesis dNN : ((0:IR)≤'d).
Hypothesis firstQuadW: (0:IR) ≤ (2*'α*'d) ≤ ½ * π.
Local Definition tr := ((Qinv α):Q).


Local Notation  αNZ := ((pos_ap_zero _ _ αPos): 'α[#](0:IR)).


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
(Also, on some wide roads, I can
make a U turn in just one maneouver. So, the
minimum turn radius is less than half the width 
of such roads. So, the minimum turn radius is
only a small factor times width of the car. Note
that in [CarDimensions], the [width] field actually
denotes half the width.)
*)
Hypothesis turnCentreOut : (Qle (width cd) tr).

(*not in use anymore?*)
Definition negY `{One A}`{Negate A} : Cart2D A:= 
{|X:=1;Y:=-1|}.


Definition NegPosition : Type := bool (*outside*) * bool(*inside*).

(** In the  "constant times cosine" explained at the  beginning of this section, the value 
in the representation, the angle β can for
the 4 coordinates can only take one of the following
4 values: *)

Require Import CartIR2.
Definition βMinusBack :(Cart2D Q) :=
({|X :=  lengthBack cd; Y := tr - width cd |}).

Definition βPlusBack :(Cart2D Q) :=
({|X :=  lengthBack cd; Y := tr + width cd |}).

Definition βMinusFront :(Cart2D Q) :=
( {|X :=  lengthFront cd; Y := tr - width cd |}).

Definition βPlusFront :(Cart2D Q) :=
( {|X :=  lengthFront cd; Y := tr + width cd |}).


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

(*Move *)
Definition flipAngle (c:Polar2D IR) : Polar2D IR:=
{| rad := rad c ; θ:= ½ * π -θ c|}.

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


Lemma WriggleFirstQSpace3 :  ∀  (confineRect: Line2D IR),
(∀ θ:IR,
(0 ≤ θ ≤ 'α * 'd
 → confineRect1 θ ⊆ confineRect)
∧ ('α * 'd ≤ θ ≤ 2 * 'α * 'd
   → confineRect2 θ ⊆ confineRect))
  <->
  carConfinedDuringAMs ('cd) confineRect SWriggle init.
Proof using All.
  intro.
  unfold confineRect2, confineRect1,
    constW1, constW2.
  rewrite <- WriggleFirstQSpace2; auto;[].
  apply iff_under_forall.
  intro θ. rewrite <- trComplicated.
  apply and_iff_compat_lr.
  eapply andWeakenL.
  exact (iff_under_imp2 _ _ _).
  apply and_comm.
  eapply andWeakenL.
  exact (iff_under_imp2 _ _ _).
  eapply andWeakenL.
  apply po_properL; eauto with typeclass_instances.
  apply and_comm.
  eapply andWeakenL.
  apply po_properL; eauto with typeclass_instances.
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
  replace (@cast _ _ (@castCart Q IR _)) with (@castCart Q IR _);[| reflexivity]. unfold castCart. simpl.
  pose proof  (@preserves_plus _ _ _ _ _ _ _ _ _ _ _ _
   (cast Q IR) _ tr) as Hh.
   unfold transpose.
   simpl.
   rewrite Hh at 1.
   rewrite Hh at 1.
   rewrite Hh at 1.
   rewrite Hh at 1.
   rewrite Hh at 1.
   rewrite Hh at 1.
   rewrite Hh at 1.
   rewrite Hh at 1.
  rewrite  preserves_negate.
  fold trr.
   unfold inprod, InProductCart2D;split; split; split; simpl;
    try IRring.
Qed.

Set Suggest Proof Using.

(** Now lets consider all 4 sides one by one. They are
too different to handle simulaneously *)
Definition isBoundLeft (minx: IR) :=
forall θ:IR,
(0 ≤ θ ≤ 'α * 'd
 → minx ≤ X (minxy (confineRect1 θ)))
∧ ('α * 'd ≤ θ ≤ 2 * 'α * 'd
   → minx ≤ X (minxy (confineRect2 θ))).

Lemma βPlusMinusBack : 
'(polarTheta βMinusBack) ≤ cast CR IR (polarTheta βPlusBack).
Abort.

Lemma βPlusMinusFront : 
'(polarTheta βMinusFront) ≤ cast CR IR (polarTheta βPlusFront).
Abort.


(* Move *)
Lemma Cart2DRadNNegIR : forall c:(Cart2D Q),
(0:IR) ≤ ' (| c |).
Proof using.
  intros.
  rewrite <- CRasIR0.
  apply CR_leEq_as_IR.
  apply Cart2PolarRadRange.
Qed.

Lemma inj_Q_nneg: forall q,
  (0:IR) ≤ 'q  <-> (Qle 0  q)%Q.
Proof using.
  intros. autounfold with IRMC.
  rewrite <- inj_Q_Zero.
  split.
  - apply leEq_inj_Q.
  - apply inj_Q_leEq.
Qed. 

Lemma divideBy2: forall c:IR,
  c = (½ * c) + (½ * c).
Proof using.
  intros. setoid_rewrite x_plus_x.
  unfold half_num. unfold HalfNumIR.
  setoid_rewrite mult_assoc_unfolded.
  rewrite (mult_commut_unfolded  _ Two).
  rewrite half_1. IRring.
Qed. 


Lemma 
CR_leEq2_as_IR: ∀ x y z: CR, (x ≤ y ≤ z) ↔ 
  (CRasIR x ≤ CRasIR y ≤ CRasIR z).
Proof using.
  intros ? ? ?. do 2 rewrite CR_leEq_as_IR.
  tauto.
Qed.
  
Lemma firstQuadβMinusBack:
 (0:IR) ≤ ' polarTheta βMinusBack ≤  (½ * π).
Proof using ntriv turnCentreOut.
  rewrite PiBy2DesugarIR.
  rewrite <- (IRasCRasIR_id (Pi [/]TwoNZ)).
  rewrite <- CRPiBy2Correct1.
  rewrite <- CRasIR0.
  apply CR_leEq2_as_IR.
  apply polarFirstQuad.
  unfold nonTrivialCarDim in ntriv.
  simpl in ntriv.
  do 3 rewrite inj_Q_nneg in ntriv.
  destruct ntriv as  [Ha Hbc]. destruct Hbc.
  split; simpl; autounfold with QMC; lra.
Qed.

(** exact same proof as above *)
Lemma firstQuadβPlusFront:
 (0:IR) ≤ ' polarTheta βPlusFront ≤  (½ * π).
Proof using ntriv turnCentreOut.
  rewrite PiBy2DesugarIR.
  rewrite <- (IRasCRasIR_id (Pi [/]TwoNZ)).
  rewrite <- CRPiBy2Correct1.
  rewrite <- CRasIR0.
  apply CR_leEq2_as_IR.
  apply polarFirstQuad.
  unfold nonTrivialCarDim in ntriv.
  simpl in ntriv.
  do 3 rewrite inj_Q_nneg in ntriv.
  destruct ntriv as  [Ha Hbc]. destruct Hbc.
  split; simpl; autounfold with QMC; lra.
Qed.


(** exact same proof as above *)
Lemma firstQuadβPlusBack:
 (0:IR) ≤ ' polarTheta βPlusBack ≤  (½ * π).
Proof using ntriv turnCentreOut.
  rewrite PiBy2DesugarIR.
  rewrite <- (IRasCRasIR_id (Pi [/]TwoNZ)).
  rewrite <- CRPiBy2Correct1.
  rewrite <- CRasIR0.
  apply CR_leEq2_as_IR.
  apply polarFirstQuad.
  unfold nonTrivialCarDim in ntriv.
  simpl in ntriv.
  do 3 rewrite inj_Q_nneg in ntriv.
  destruct ntriv as  [Ha Hbc]. destruct Hbc.
  split; simpl; autounfold with QMC; lra.
Qed.

(** exact same proof as above *)
Lemma firstQuadβMinusFront:
 (0:IR) ≤ ' polarTheta βMinusFront ≤  (½ * π).
Proof using ntriv turnCentreOut.
  rewrite PiBy2DesugarIR.
  rewrite <- (IRasCRasIR_id (Pi [/]TwoNZ)).
  rewrite <- CRPiBy2Correct1.
  rewrite <- CRasIR0.
  apply CR_leEq2_as_IR.
  apply polarFirstQuad.
  unfold nonTrivialCarDim in ntriv.
  simpl in ntriv.
  do 3 rewrite inj_Q_nneg in ntriv.
  destruct ntriv as  [Ha Hbc]. destruct Hbc.
  split; simpl; autounfold with QMC; lra.
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
  unfold isBoundLeft.
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

(* Move *)
Lemma CosMinusSwap : forall a b:IR,
  Cos (a - b) = Cos (b - a).
Proof using.
  intros ? ?.
  rewrite <- Cos_inv.
  apply Cos_wd.
  IRring.
Qed.

Lemma Pi_minus_Sin: ∀ θ : ℝ, 
  Sin (π - θ) = (Sin θ).
Proof using.
  intros ?.
  rewrite negate_swap_r.
  autounfold with IRMC.
  rewrite  Sin_inv.
  unfold π, Pi_Instance_IR.
  fold (θ [-] Pi).
  rewrite Sin_minus_Pi.
  ring.
Qed.


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
Lemma maxTurnNeededConjecture (minx maxx miny: IR) :
((½ * π ) ≤ (' polarTheta βPlusFront + ' polarTheta βPlusBack))
→
isMaxTurnNeeded ('polarTheta βPlusFront).
Proof using firstQuadW ntriv turnCentreOut.
  intro Has. simpl.
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
->
((½ * π )
≤ (' polarTheta βPlusFront + ' polarTheta βPlusBack)).
Abort.

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


(** derive [firstQuadW] from this.*)
Hypothesis maxNeededTurn 
  : (0 : ℝ) ≤ 2 * ' α * ' d ≤ (' polarTheta βPlusFront).

Definition leftBound : IR :=
let m1 := (X (minxy (confineRect1 0))) in 
let m2 := (X (minxy (confineRect2 (2 * 'α * 'd)))) in 
(min m1 m2).

Lemma leftBoundCorrect: 
isBoundLeft leftBound.
Proof using All.
  unfold leftBound.
  intros θ.
  split.
  - intros H.
    eapply transitivity;[apply Min_leEq_lft|].
    eapply confineRect1LeftMonotoneRight;
      [reflexivity| |].
    + split;[reflexivity|].
      rewrite PiBy2DesugarIR. apply PiBy2Ge0.
    + eapply firstQuadW1; eauto. 
  - simpl.
    intros H.
    eapply transitivity;[apply Min_leEq_rht|].
    simpl.
    apply (@order_preserving _ _ _ _ _ _ _ _).
    apply flip_le_negate.
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
    rewrite CosMinusSwap.
    setoid_rewrite CosMinusSwap at 2.
    apply Cos_resp_leEq.
    + apply flip_le_minus_l.
      rewrite negate_involutive.
      setoid_rewrite plus_0_l.
      eapply transitivity;[|
        apply FrontLeBack].
      tauto.
    + rewrite (divideBy2 Pi).
      apply plus_le_compat;
        [apply firstQuadβPlusBack|].
      rewrite PiBy2DesugarIR.
      apply flip_le_negate.
      rewrite negate_involutive.
      eapply transitivity;[
        apply MinusPiBy2Le0|].
        destruct H.
      eapply transitivity;[|apply H].
      apply adNN; eauto.
    + apply (@order_preserving _ _ _ _ _ _ _ _).
      apply flip_le_negate.
      tauto.
Qed.

Lemma LeftBoundEqSimpl : leftBound = 
(min (- ' lengthBack cd)
  (' tr * (2 * Sin (' α * ' d)) -
   (' lengthBack cd * cos (2 * ' α * ' d) +
    ' (tr + width cd) * sin (2 * ' α * ' d)))).
Proof using.
  match goal with
  [|- _= ?r] => remember r as rr
  end.
  unfold leftBound.
  simpl.
  rewrite plus_0_l.
  fold CosClassIR.
  fold (@cos IR _).
  rewrite <- unitVDot.
  rewrite <- unitVDot2.
  do 2 rewrite multDotRight.
  pose proof CartToPolarCorrect as H.
  simpl in H. unfold norm, NormCart2DQ in H.
  rewrite <- H.
  rewrite <- H.
  unfold inprod, InProductCart2D.
  simpl. 
  rewrite Cos_zero.
  rewrite Sin_zero.
  unfold trr.
  subst rr. 
  apply Min_wd_unfolded; split; simpl; try IRring.
Qed.

Definition isBoundRight (maxx: IR) :=
forall θ:IR,
(0 ≤ θ ≤ 'α * 'd
 → X (maxxy (confineRect1 θ)) ≤ maxx)
∧ ('α * 'd ≤ θ ≤ 2 * 'α * 'd
   →  X (maxxy (confineRect2 θ)) ≤ maxx).

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
Lemma rightBoundCorrect 
  : isBoundRight rightBound.
Proof using dNN firstQuadW lengthFrontGreater maxNeededTurn ntriv ntrivStrict turnCentreOut αPos. 

  unfold isBoundRight, rightBound.
  intro. simpl.
  split; intro Hb.
  - do 2 rewrite plus_0_l.
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
    rewrite CosMinusSwap.
    setoid_rewrite CosMinusSwap at 2.
    apply Cos_resp_leEq.
    + apply flip_le_minus_l.
      rewrite negate_involutive.
      setoid_rewrite plus_0_l.
      eapply transitivity;[|
        apply maxNeededTurn].
      rewrite <- (@simple_associativity _ _ plus _ _).
      apply rings.RingLeProp2.
      destruct Hb. eapply transitivity; eauto.
    + rewrite (divideBy2 Pi).
      apply plus_le_compat;
        [apply firstQuadβPlusFront|].
      rewrite PiBy2DesugarIR.
      apply flip_le_negate.
      rewrite negate_involutive.
      eapply transitivity;[
        apply MinusPiBy2Le0|].
      apply Hb.
    + apply (@order_preserving _ _ _ _ _ _ _ _).
      apply flip_le_negate.
      tauto.
  - rewrite plus_0_l.
    rewrite <- transitionMaxX.
    apply (@order_preserving _ _ _ _ _ _ _ _).
    apply (@order_preserving _ _ _ _ _ _ _);
      [apply OrderPreserving_instance_0;
       apply Cart2DRadNNegIR |].
    apply Cos_resp_leEq.
    + apply plus_resp_nonneg;[|apply firstQuadβMinusFront].
      apply adNN; auto.
    + rewrite (divideBy2 Pi).
      apply plus_le_compat;[|apply firstQuadβMinusFront].
      eapply transitivity;[apply Hb|]. tauto.
   + apply plus_le_compat;[tauto| reflexivity].
Qed.

Definition isBoundBottom (miny: IR) :=
forall θ:IR,
(0 ≤ θ ≤ 'α * 'd
 → miny ≤ Y (minxy (confineRect1 θ)))
∧ ('α * 'd ≤ θ ≤ 2 * 'α * 'd
   → miny ≤ Y (minxy (confineRect2 θ))).

(** Based on intuition, which may be corrupted with
some assumptions not yet made explicity 

Definition bottomBound2 : IR :=
  (Y (minxy (confineRect2 (2 * 'α * 'd)))).
*)

Lemma bottomBound2Correct : 
let miny := (Y (minxy (confineRect2 (2 * 'α * 'd)))) in
forall θ:IR,
 'α * 'd ≤ θ ≤ 2 * 'α * 'd
   → miny ≤ Y (minxy (confineRect2 θ)).
Proof using dNN firstQuadW ntriv turnCentreOut αPos. 
  unfold isBoundRight, rightBound.
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

Lemma bottomBound1Correct : 
let miny := (Y (minxy (confineRect1 ('α * 'd)))) in
 ('α * 'd ≤ (½ * π - ' polarTheta βPlusBack))
->
forall θ:IR,
 0 ≤ θ ≤ 'α * 'd
   → miny ≤ Y (minxy (confineRect1 θ)).
Proof using dNN firstQuadW ntriv turnCentreOut αPos. 
  simpl. intros Hu ?. simpl.
  intro Hb.
  pose proof (firstQuadW1 _ αPos _ dNN firstQuadW _  Hb)
    as Ht.
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

End FirstQuadWriggleQ.