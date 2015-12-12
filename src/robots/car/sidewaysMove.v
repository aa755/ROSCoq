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
Require Import atomicMoves.

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
Context {maxTurnCurvature : Qpos}
(acs : AckermannCar maxTurnCurvature).
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
  Variable tc : IR.
  Hypothesis tcNZ : tc[#]0.
  Variable distance : IR.
  

(** In our formalism, wriggle is a composition of the following 2 atomic moves.
  *)
  
  Definition steerAndDrive : AtomicMove
    := {|am_tc := tc; am_distance := distance |}.
  Definition revSteerAndrevDrive : AtomicMove
    := {|am_tc := -tc; am_distance := -distance |}.

(** the distance covered during driving and reverse driving is exactly the same.
  TODO: let them be slightly different, e.g. upto epsilon
 *)
  Definition Wriggle : AtomicMoves 
    :=  [steerAndDrive; revSteerAndrevDrive].
  
  Variable tstart : Time.
  Variable tend : Time.
  Hypothesis timeInc : tstart ≤ tend.
  
  (** Now, we assume that the car executes the [Wriggle] move from time [tstart] to [tend],
    and characterize the position and orientation at [tend], in terms of their values at [tstart]. 
     In this document When we say "move" in natural language, we mean [AtomicMoves].
    *)
  Hypothesis amsc : CarExecutesAtomicMovesDuring acs Wriggle tstart tend 
                      (timeInc).
  
  
  Local Notation θs := ({theta acs} tstart).
  Local Notation Xs := ({X (position acs)} tstart).
  Local Notation Ys := ({Y (position acs)} tstart).

  
  Hint Unfold One_instance_IR : IRMC.
      
      
  
  Lemma Wriggleθ : {theta acs} tend =  θs + 2 * tc * distance.
  Proof using amsc.
    invertAtomicMoves. rename Hf into amscrl.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl. rewrite amscl in amscrl.
    rewrite amscrl.
    autounfold with IRMC. ring.    
  Qed.

  (** just to show that the car doesn't end up to the initial position after wriggle.
     This equation is not needed for anything else. *)
  Lemma WriggleX : {X (position acs)} tend =  Xs +
        ((2* Sin (θs + tc * distance) 
            - Sin (θs + 2 * tc * distance)  - Sin θs) [/] tc [//] tcNZ).
  Proof using All.
    pose proof Wriggleθ as XX.
    invertAtomicMoves.
    rename amscl into Hl.
    rename Hf into Hrr.
    pose proof Hl as Hlt.
    apply AtomicMoveθ in Hlt.
    apply AtomicMoveX with (tcNZ0:= tcNZ) in Hl.
    apply AtomicMoveXT with (tcNZ0:= tcnegNZ _ tcNZ) in Hrr.
    Local Opaque Cos Sin.
    simpl in Hl, Hrr, Hlt.
    unfold cf_div in Hrr.
    rewrite XX in Hrr.
    rewrite Hrr. rewrite Hl.
    autounfold with IRMC. unfold cf_div.
    rewrite reciprocalNeg with (xp:=tcNZ).
    rewrite cring_inv_mult_lft.
    rewrite <- cring_inv_mult_rht.
    setoid_rewrite minusInvR.
    rewrite Hlt.
    autounfold with IRMC. unfold cg_minus. simpl.
     ring.
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

Context {maxTurnCurvature : Qpos}
(acs : AckermannCar maxTurnCurvature).

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
  Variable tc : IR.
  Hypothesis tcNZ : tc[#]0.
  Variable wdistance : IR.
  Variable ddistance : IR.
  
  Local Notation SWriggle := (Wriggle tc wdistance).
  Local Notation SWriggleInv := (AtomicMovesInv SWriggle).
  
  (** Drive a distance of [ddistance]
    with front wheels perfectly straight.*)  
  Local Notation DriveStraight := {| am_distance := ddistance ; am_tc := 0|}.

  Definition SidewaysAux : AtomicMoves 
    := SWriggle ++ [DriveStraight] ++ SWriggleInv.

  
  (** The car's orientation at the end is same as that at the start.
     [θAtW] denotes the car's orientation at the completion of the [SWriggle] move. 
     For any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
     *)
  Lemma SidewaysAuxState : forall  (tstart tend : Time) (timeInc : tstart ≤ tend),
  (CarExecutesAtomicMovesDuring acs SidewaysAux tstart tend timeInc)
  ->
  let θs := ({theta acs} tstart) in 
  let θAtW := θs + 2 * tc * wdistance  in
  {theta acs} tend =  θs /\
    posAtTime acs tend = (posAtTime acs tstart)
      + ('ddistance) * (unitVec θAtW).
  Proof using Type.
    intros ? ? ? amsc.    
    unfold SidewaysAux in amsc.
    apply movesControlsApp in amsc.
    destruct amsc as [tds Hams]. (* ds for drive straight *)
    destruct Hams as [pds Hams].
    repnd. rename Hamsl into Hw. (* w for wiggle *)
    apply movesControlsApp in Hamsr.
    destruct Hamsr as [twr Hamsr]. (* ds for drive straight *)
    destruct Hamsr as [pwr Hams]. repnd.
    rename Hamsl into Hds.
    rename Hamsr into Hwr.
    pose proof Hw as Hwb. (* needed for θAtW *)
    eapply atomicMovesInvertible in Hw; eauto.
    specialize (Hw Hwr). clear Hwr.
    apply Wriggleθ in Hwb.
    invertAtomicMoves.
    apply AtomicMoveZFinal in Hf;[|unfold amNoTurn;  reflexivity].
    simpl in Hf. repnd.
    specialize (Hw Hfl).
    repnd. symmetry in Hwr.
    split;[assumption|]. rewrite Hwb in Hfr.
    clear Hwb Hwr Hfl pll. rewrite Hfr in Hwl. clear Hfr.
    rewrite  <- (@plus_assoc (Cart2D IR)) in Hwl; [|eauto with typeclass_instances].
    apply (@left_cancellation ) in Hwl; [|apply groups.LeftCancellation_instance_0].
    apply (RingNegateProper ) in Hwl.
    rewrite negate_involutive in Hwl.
    rewrite Hwl. ring.
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
    := {| am_distance := - ddistance * Cos (2 * tc * wdistance) ; am_tc := 0|}.

  Definition SidewaysMove : AtomicMoves 
    := SidewaysAux ++ [DriveStraightRev].
    
  (** The car's final orientation is same as before, and 
  its position changes in the direction that is at a right angle [(½ * π)]
  to its orientation, i.e., it is a sideways move. 
  The distance moved is [ddistance * Sin  θw].

  As mentioned before, for any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
  *)
  
  Lemma SidewaysState : forall  (tstart tend : Time) (timeInc : tstart ≤ tend),
  (CarExecutesAtomicMovesDuring acs SidewaysMove tstart tend timeInc)
  ->
  let θs := ({theta acs} tstart) in 
  let θw := 2 * tc * wdistance  in
    {theta acs} tend =  θs /\
    posAtTime acs tend = (posAtTime acs tstart) 
      + ('(ddistance * Sin  θw)) * unitVec (θs + (½ * π)).
  Proof using Type.
    intros ? ? ? amsc.
    unfold SidewaysMove in amsc. simpl.
    apply movesControlsApp in amsc.
    destruct amsc as [tds Hams]. (* ds for drive straight *)
    destruct Hams as [pds Hams]. repnd.
    apply SidewaysAuxState in Hamsl.
    invertAtomicMoves.
    apply AtomicMoveZFinal in Hf;[|unfold amNoTurn;  reflexivity].
    simpl in Hf. repnd.
    rewrite Hamsll in Hfl.
    rewrite Hamsll in Hfr.
    split;[assumption|]. clear Hamsll Hfl.
    rewrite Hamslr in Hfr. clear Hamslr pll pdsl pdsr.
    remember (2 * tc * wdistance) as θw.
    clear Heqθw. unfold cast, castCRCart2DCR in Hfr.
    rewrite <- sameXYMult in Hfr.
    rewrite sameXYNegate in Hfr.
    rewrite  <- (@mult_assoc (Cart2D IR)) in Hfr ; [|eauto with typeclass_instances].
    
    rewrite <- negate_mult_distr_l in Hfr.
    rewrite negate_mult_distr_r in Hfr.
    rewrite  <- (@plus_assoc (Cart2D IR)) in Hfr; [|eauto with typeclass_instances].
    setoid_rewrite  <- (@plus_mult_distr_l (Cart2D IR)) in Hfr;
       [|eauto with typeclass_instances].
    rewrite unitVecLemma1 in Hfr. unfold cast, castCRCart2DCR.
    rewrite <- sameXYMult.
    rewrite  <- (@mult_assoc (Cart2D IR)); [|eauto with typeclass_instances].
    rewrite PiBy2DesugarIR.
    exact Hfr.
  Qed.

End Sideways.
