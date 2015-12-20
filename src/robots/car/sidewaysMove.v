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
(** Because cartesian to polar conversion is currently
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
Notation tr := ((Qinv α):Q).


Local Notation  αNZ := ((pos_ap_zero _ _ αPos): 'α[#](0:IR)).


Local Definition trComplicated : 'tr = f_rcpcl ('α) αNZ.
Proof using αPos.
  pose proof αPos as Hh.
  eapply less_wdl in Hh;[|symmetry;apply inj_Q_Zero].
  apply less_inj_Q in Hh. simpl in Hh.
  assert (tr == Qdiv 1 α)%Q as H by (field;lra).
  rewrite H. setoid_rewrite inj_Q_div with (H:=αNZ).
  unfold cf_div.
  rewrite  inj_Q_One.
  unfold cast, Cast_instace_Q_IR.
  unfold Q2R.
  IRring.
Qed.

(** the turn center cannot be inside the car. for that,
one of the front wheels have to rotate by more than 90 along 
the vertical axis*)
Hypothesis turnCentreOut : (width cd ≤Qabs tr)%Q.

(** all coordinates below in the second coordinates
are non-negative. This is to ensure that
the result of polar conversion is in the first quadrant.
*)
 
Definition negY `{One A}`{Negate A} : Cart2D A:= 
{|X:=1;Y:=-1|}.


Definition NegPosition : Type := bool (*outside*) * bool(*inside*).

(** see  [decodeAsCosXY] below to see what the next 4 definitions represent *)

Definition minXY1 : (Cart2D NegPosition) * (Cart2D (Cart2D Q)):=
( {|X := (true, true); Y :=(true, false)|},
{| X := {|X :=  lengthBack cd; Y := tr - width cd |};
   Y := {|X :=  tr + width cd; Y :=  lengthBack cd |}
|}).

Definition maxXY1 : (Cart2D NegPosition) * (Cart2D (Cart2D Q)):=
({|X := (false, false); Y :=(true, true)|},
{| X := {|X := lengthFront cd; Y := tr + width cd |};
   Y := {|X :=  tr - width cd; Y :=  lengthFront cd |}
|}).


Definition minXY2 : (Cart2D NegPosition) * (Cart2D (Cart2D Q)):=
({|X := (true, false); Y := (false, true)|},
{| X := {|X :=  lengthBack cd; Y := tr + width cd |};
   Y := {|X :=  tr - width cd; Y :=  lengthBack cd |}
|}).


Definition maxXY2 : (Cart2D NegPosition) * (Cart2D (Cart2D Q)):=
({|X := (false, true) ; Y :=(false, false)|},
{| X := {|X := lengthFront cd; Y := tr - width cd |};
   Y := {|X :=  tr + width cd; Y :=  lengthFront cd |}
|}).

Definition negateIfTrue `{Negate A} (b:bool)(a:A) : A:=
if b then (-a) else a.

Require Import CartIR2.
Definition decodeAsCos (n:NegPosition) (c:Cart2D Q) (θ:IR): IR :=
let β :IR := '(polarTheta c) in
let γ := θ + (negateIfTrue (negb (snd n)) β) in
(negateIfTrue (fst n) (∥c∥ * Cos γ)).

Definition decodeAsCosXY (nc: (Cart2D NegPosition) * (Cart2D (Cart2D Q))) (θ:IR): Cart2D IR :=
{|X := decodeAsCos (X (fst nc)) (X (snd nc)) θ;
  Y := decodeAsCos (Y (fst nc)) (Y (snd nc)) θ|}.

Local Notation init  := (0:Rigid2DState IR).
Local Notation SWriggle := (Wriggle ('α) αNZ ('d)).


Local Definition trr :IR := 'tr.
Lemma multDotRight : forall (a:IR) (b c : Cart2D IR),
a * (⟨b,c⟩) = ⟨('a) * c, b⟩.
Proof using.
  intros.   unfold inprod, InProductCart2D.
  simpl. IRring.
Qed.
Global Instance srmInjQ : SemiRing_Morphism (cast Q IR).
Proof using.
repeat (split; try apply _).
- intros. apply inj_Q_plus.
- intros. apply inj_Q_Zero.
- intros. apply inj_Q_mult.
- intros. apply inj_Q_One.
Qed.

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
  do 8 (rewrite <- CartToPolarCorrect).
  replace (@cast _ _ (@castCart Q IR _)) with (@castCart Q IR _);[| reflexivity]. unfold castCart. simpl.
  rewrite  preserves_plus.
  rewrite  preserves_plus.
  rewrite  preserves_negate.
  fold trr.
   unfold inprod, InProductCart2D;split; split; split; simpl;
    try IRring.
Qed.

End FirstQuadWriggleQ.
