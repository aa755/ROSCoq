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
Require Import CRMisc.numericalOpt.


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
Require Import robots.car.sidewaysMove.
Require Import MathClasses.implementations.bool.

(** In [sidewaysMove], we analyzed the space needed to execute
a sideways move, which is specified by 3 parameters.
To implement such a move, one has to invert that equation --
given the amount of available space, find a best
choice of those 3 parameters.
We fix one of those by deciding that while turning, the
steering wheel will be at its extremities -- this choice
may be optimal.

2 parameters remain : how much to drive while turning (d),
and how much to drive while moving straight (d').

The total X-space needed can be decomposed as a sum
of 2 terms, each of which is a function of d and d'. 
The former, which is
the space needed to execute the [Wriggle] part of the sideways move,
is a horrendous quartic.

The latter function, which
is the X-space consumed by the straight move, and is easily
invertible w.r.t. d'. Hence we chose d' such that all the
remaining space (if any) is
taken up by the straight move.

So, the only remaining parameter is d. We systematically try several
samples and pick the best one that is safe.
Based on the how closely the samples are chosen for d, this approach
is both sound and approximately optimal.
*)

Definition mkQTurnMove (α:Qpos) (d:CR): DAtomicMove CR.
  exists {|am_distance := d ; am_tc := '`α|}.
  simpl. right. right.
  exists α. simpl. 
  fold (CRopp).
  fold (CRplus).
  fold (@negate CR _).
  fold (@plus CR _).
  rewrite minus_0_r.
  reflexivity.
Defined.


Definition mkNegQTurnMove (α:Qpos) (d:CR): DAtomicMove CR.
  exists {|am_distance := d ; am_tc := -'`α|}.
  simpl. right. left.
  exists α. simpl. 
  fold (CRopp).
  fold (CRplus).
  fold (@negate CR _).
  fold (@plus CR _).
  rewrite negate_involutive.
  rewrite plus_0_l.
  reflexivity.
Defined.

Definition mkQWriggle (α:Qpos) (d:CR) : list (DAtomicMove CR) 
    :=  [mkQTurnMove α d; mkNegQTurnMove α (-d)].

Require Import robots.car.commutator.
Definition mkQSideways (α:Qpos) (d d':CR) : list (DAtomicMove CR) 
    := 
conjugate [mkStraightMove d'] (mkQWriggle α d).

(*
Lemma DWriggleSame : forall (t:Qpos) (d:CR), 
  List.map getAtomicMove (DWriggle t d) = Wriggle ('t) d.
Proof.
  intros. reflexivity.
Qed.


Lemma DSidewaysSame : forall (t:Qpos) (dw ds :CR), 
  List.map getAtomicMove (DSideways t dw ds) = SidewaysMove ('t) dw ds.
Proof.
  intros. reflexivity.
Qed.
*)

Section InverseProblem.

Variable cd : CarDimensions Q.


Hypothesis ntriv : nonTrivialCarDim cd.

Variable  α : Q.
Hypothesis αPosQ : (0<α).


(** there is already a ring instance decrared for CR,
 using the legacy
 definition of ring. That may cause issues.
 Remove that ring, because that needs unfolding to ugly 
legacy notations for the old [CRing].
Add the old ring declaration to a separate file, and 
import it in old files.
 *)
Add Ring tempRingCR : (stdlib_ring_theory CR).

Let αPos : ((0:IR)[<]'α).
Proof using αPosQ.
  eapply less_wdl;[| apply inj_Q_Zero].
  apply inj_Q_less. apply αPosQ. 
Qed.

Let tr :=  Qinv α.

Hint Resolve  αPos : sideways.
Let αNZ := ((pos_ap_zero _ _ αPos): 'α[#](0:IR)).

Let trComplicated : 'tr = f_rcpcl ('α) αNZ.
Proof using ntriv.
 apply QinvIRinv.
Qed.

(** The turn center cannot be inside the car. for that,
one of the front wheels have to rotate by more than 90 along 
the vertical axis. 
*)
Hypothesis turnCentreOut : ((width cd) <= tr)%Q.

Local Definition βMinusBack : Cart2D Q := CornerAngles.βMinusBack cd tr.
Local Definition βMinusFront : Cart2D Q := CornerAngles.βMinusFront cd tr.
Local Definition βPlusBack : Cart2D Q := CornerAngles.βPlusBack cd tr.
Local Definition βPlusFront : Cart2D Q := CornerAngles.βPlusFront cd tr.

(** extra space available t execute the sideways move *)
Variable Xs : Q.
Hypothesis Xsp : (0<Xs).

(** space needed for the wriggle move for a given θ. The parameter
[d] that we are after is just [θ/α] *)
Let extraSpaceX1W  (θ:CR) : CR := 
  compress (sidewaysMove.extraSpaceX1 α cd θ).


(** Recap:
[extraSpaceX1W] is valid only for 
when [(α * d)] is  between 0 and [leftCriticalAngle].
There is also an [extraSpaceX2] for the case when
[(α * d)] is between [leftCriticalAngle]
and [(polarTheta βPlusBack)/2], however that 
range may be so small for most cars, that 
it is not worth analysing that equation.
For mazda 3, the range was 2 degrees.
Beyond [(polarTheta βPlusBack)/2], the problem
becomes trivial, and can be solved in just 1 move.
*)

Let leftCriticalAngle : CR := 
  sidewaysMove.leftCriticalAngleCR  α cd.

Definition extraSpaceX1WValid (θ:CR) : Prop :=
0 ≤ θ ≤ leftCriticalAngle
∧ 2 * θ ≤ (polarTheta βPlusBack).

Definition maxValidAngle : CR :=
  min (leftCriticalAngle) (½*(polarTheta βPlusBack)).

Require Import MCMisc.fields.
Require Import MCMisc.rings.



Lemma extraSpaceX1WValidIff (θ:CR) : 
extraSpaceX1WValid θ
↔ 0 ≤ θ ≤ maxValidAngle.
Proof using.
  unfold extraSpaceX1WValid, maxValidAngle.
  rewrite halfLeShift.
  split; intro h;
   dands; try tauto.
- apply CRmin_glb; [apply h; fail| tauto].
- eapply transitivity;[|eapply CRmin_lb_l].
  apply h.
- eapply transitivity;[|eapply CRmin_lb_r].
  apply proj2 in h.
  exact h.
Qed.

(** the srict inequality in the 
last clause is necessary, because we want 
same space to be left for the straight move,
to ensure that 
the upward shift is nonzero. *)
Definition dAdmissibleXwise (θ:CR) :=
extraSpaceX1WValid θ
∧ extraSpaceX1W θ < 'Xs.

(** we need to often compare reals. This can
 -only be done upto a finte (but arbitrary) accuracy.*)
Variable eps : Qpos.

Definition approxDecideXAdmiss (θ:CR) : bool :=
approxDecLtRQ eps (extraSpaceX1W θ) Xs.



Require Import MCMisc.rings.

Let trPos : 0 < tr.
Proof using αPosQ.
apply Qinv_lt_0_compat.
exact αPosQ.
Qed.


Lemma cosβPlusBackPos :
 0 < cos (polarTheta βPlusBack).
Proof using Xsp ntriv trComplicated turnCentreOut.
  apply pos_cos_CR.
  unfold nonTrivialCarDim in ntriv.
  split. eapply (proj1 (polarFirstQuad _ _)).
  apply polarFirstQuadStrict; simpl;  autounfold with QMC in *; 
  simpl; try lra.
  Unshelve.
  split; simpl;  autounfold with QMC in *; try lra.
Qed.


Definition cosβPlusBackPosWitness : Qpos.
Proof using ntriv tr trPos.
  exists (lengthBack cd /(tr + width cd + lengthBack cd))%Q.
  unfold nonTrivialCarDim in ntriv.
  autounfold with QMC in *.
  apply Qlt_shift_div_l; lra.
Defined.

  (** hypotenuse  ≤ sum of the other sides of a right angled triangle*)
Lemma cosβPlusBackPosT_subproof:
(' cosβPlusBackPosWitness <= cos (polarTheta βPlusBack) - 0%mc)%CR.
Proof using Xsp ntriv trComplicated trPos turnCentreOut. 
  setoid_rewrite preserves_0.
  fold (CRopp).
  fold (CRplus).
  fold (@negate CR _).
  fold (@plus CR _).
  rewrite minus_0_r.
  pose proof (Cart2Polar2CartID βPlusBack) as H.
  destruct H as [Hx _].
  simpl in Hx.
  simpl.
  unfold nonTrivialCarDim in ntriv.
  autounfold with QMC in ntriv, trPos.
  apply (@order_reflecting _ _ _ _  _ _ (mult ('(tr + width cd + lengthBack cd)))).
    apply OrderReflecting_instance_0. apply preserves_pos.
    unfold PropHolds. autounfold with QMC. lra.

  fold (cast Q CR).
  rewrite <- preserves_mult.
  assert (
  ((tr + width cd + lengthBack cd) * (lengthBack cd / (tr + width cd + lengthBack cd))%Q)
  == (lengthBack cd ))%Q as Heq by (field; lra).
  setoid_rewrite Heq. clear Heq.
  rewrite Hx. clear Hx.
  apply mult_le_compat;[apply Cart2PolarRadRange 
    | apply lt_le, cosβPlusBackPos
    | 
    |  reflexivity]; [].
  apply RingLeIfSqrLe.
- apply RingPosNnegCompatPlus;[| apply Cart2PolarRadRange].
  apply preserves_pos. autounfold with QMC in *. unfold PropHolds; lra.

- unfold sqr.
  rewrite <- preserves_mult.
  setoid_rewrite CRsqrt_sqr1Q1.
  apply (@order_preserving _ _ _ _ _ _ _ _ _ _ ).
  simpl.
  rewrite nat_pow.nat_pow_2.
  rewrite nat_pow.nat_pow_2.
  remember (tr + width cd).
  fold (sqr (y + lengthBack cd)).
  fold (sqr y).
  fold (sqr (lengthBack cd)).
  apply RingLeSqr1; autounfold with QMC in *; subst; lra.
Qed.


Lemma cosβPlusBackPosT :
 (0 < cos (polarTheta βPlusBack))%CR.
Proof using Xsp ntriv trComplicated trPos turnCentreOut. 
  exists cosβPlusBackPosWitness.
  (** now we can invoke opaque lemmas.
  Even if everything in the the above [cosβPlusBackPos] opaque version
  was made transparent recursively, the witness may not be as simple/fast
  as the one above
   *)
  apply cosβPlusBackPosT_subproof.
Defined.

Lemma extraSpaceX1WValidCosPos :forall  (θ:CR),
extraSpaceX1WValid θ
→ 0 < cos (2 * θ).
Proof  using αPosQ ntriv.
  intros ? Hv.
  apply pos_cos_CR.
  unfold extraSpaceX1WValid in Hv.
  split;[apply RingLeProp3; tauto|].
  eapply le_lt_trans; [apply Hv|].
  unfold nonTrivialCarDim in ntriv.
  apply polarFirstQuadStrict; simpl;  autounfold with QMC in *; 
  simpl; try lra.
Qed.

(** needed because we wish to divide by [cos (2 * θ)]
  To avoid carrying the proof positivity, a dummy max is used.
  [extraSpaceX1WValid θ] implies that the max is equal to its right argument.
Lemma extraSpaceX1WValidCosPos :forall  (θ:CR),
 (0 < max (cos (polarTheta βPlusBack)) (cos (2 * θ)))%CR.
Proof using Xsp ntriv trComplicated trPos turnCentreOut. 
  intros ? .
  exists cosβPlusBackPosWitness.
  eapply transitivity;[apply cosβPlusBackPosT_subproof|].
  setoid_rewrite preserves_0.
  fold (CRopp).
  fold (CRplus).
  fold (@negate CR _).
  fold (@plus CR _).
  rewrite minus_0_r.
  rewrite minus_0_r.
  apply CRmax_ub_l.
Defined.
 *)

Section objective.

Variable θ:CR.

(** Now compute the quality (the amount of upward shift) for a
given parameter [d]. The remaining space, which must be positive for 
admissible values, will be used up for the straight move.
This function will only be used for admissible
[d]s -- if that simplifies anything .

[d'] is the distance covered during the straight move
*)

Hypothesis valid : extraSpaceX1WValid θ.

Let  cos2θ_lb :Qpos.
destruct (CRlt_Qmid 0 (cos (polarTheta βPlusBack))
cosβPlusBackPosT).
exists x. 
destruct p.
apply Qlt_from_CRlt in c.
assumption.
Defined.


Local Opaque CR.

Lemma  cos2θ_lbCorrect:
 '`cos2θ_lb ≤ (cos (2 * θ)).
Proof using valid.
  subst cos2θ_lb.
  destruct  (CRlt_Qmid 0 (cos (polarTheta βPlusBack))).
  simpl.
  apply snd in p.
  apply CR_lt_ltT in p.
  apply lt_le in p.
  eapply transitivity;[apply p|].
  unfold extraSpaceX1WValid in valid.
  apply CRcos_resp_leEq; try tauto;[|].
- apply RingLeProp3; tauto.
- apply Cart2PolarAngleRange.
Qed.

Let cos2θ_inv : CR.
  apply (CRinvT 
          (max ('(`cos2θ_lb))  (cos (2 * θ)))).
  right.
  exists cos2θ_lb.
  fold (CRopp).
  fold (CRplus).
  fold (@negate CR _).
  fold (@plus CR _).
  setoid_rewrite preserves_0.
  rewrite minus_0_r.
  apply CRmax_ub_l.
Defined.

Require Import MCMisc.tactics.

(** the RHS is a formula of MathClasses.abstract_algebra.Field, so
that the general field lemmas can be used *)
Lemma  cos2θ_inv_simpl : 
cos2θ_inv = (// (cos (2 * θ)) ↾ (or_intror (extraSpaceX1WValidCosPos _ valid))).
Proof using.
  unfold cos2θ_inv.
  rewrite CRinv_CRinvT.
  apply fields.recip_proper_alt.
  apply  CRle_max_r.
  apply cos2θ_lbCorrect.
Qed.

Definition spaceNeededFor1MoveSoln : CR :=
  rad ('(βPlusFront)) - '(lengthFront cd).

Definition dStraight  : CR := (compress cos2θ_inv) * ('Xs -  (extraSpaceX1W θ)).

Local Notation d' := dStraight.

Require Import MathClasses.theory.fields.



Definition dWriggle :CR := ('tr*θ).

Local Notation d := dWriggle.

Let sidewaysMove : list (DAtomicMove IR) 
  := SidewaysAux ('α) αNZ ('d) ('(d')).

Definition sidewaysMoveQCR : list (DAtomicMove CR) 
  := mkQSideways (α ↾ αPosQ) d d'.

Lemma  θcorrect : θ = 'α * d.
Proof using αPosQ.
  unfold dWriggle.
  rewrite  (@simple_associativity _ _ mult _ _).
  rewrite <- preserves_mult.
  subst tr.
  autounfold with QMC in *.
  field_simplify ((α * / α)%Q);[| lra].
  change ((1 / 1)%Q) with (@one Q _).
  rewrite preserves_1.
  fold (@mult CR _).
  rewrite mult_1_l.
  reflexivity.
Qed.
  

(** the above sideways move takes up all the available space in the X direction *)
Lemma sidweaysXSpaceExact :
   extraSpaceXSidewaysCase1  α cd d d' = 'Xs.
Proof using cos2θ_inv valid.
  unfold extraSpaceXSidewaysCase1.
  unfold d'.
  rewrite MultShuffle3r.
  rewrite compress_correct, cos2θ_inv_simpl.
  unfold cos, implCR.CosClassCR .
  setoid_rewrite <- (@simple_associativity _ _ mult _ 2 _ _) at 3.
  setoid_rewrite <- θcorrect at 2.
  rewrite reciperse_altL.
  unfold extraSpaceX1W.
  unfold extraSpaceX1.
  unfold cos, implCR.CosClassCR .
  rewrite compress_correct.
  setoid_rewrite <- θcorrect.
  ring.
Qed.

Definition upwardShift : CR := d' * (sin (2 * θ)).

Lemma upwardShiftEq1 :
let pf :=  (or_intror (extraSpaceX1WValidCosPos _ valid)) in
upwardShift =
(// (cos (2 * θ)) ↾ pf) * ('Xs -  (extraSpaceX1W θ)) * (sin (2 * θ)).

(* essentially, [upwardShift =  (tan (2 * θ)) * ('Xs -  (extraSpaceX1W θ))] .

tan is not defined for CR. Unlike sine and cosine, it has a limited domain, and thus 
would have needed a dependent argument like the one on IR
*)
Proof using.
  simpl. unfold upwardShift, d'.
  rewrite compress_correct, cos2θ_inv_simpl.
  reflexivity.
Qed.

Lemma upwardShiftCorrect: forall init,
θ2D init =0 
→ 
Y (pos2D (stateAfterAtomicMoves sidewaysMove init))
  = 
Y (pos2D init) + 'upwardShift.
Proof using.
  intros ? h0.
  unfold sidewaysMove.
  rewrite SidewaysAuxState.
  unfold sidewaysDisp, upwardShift.
  simpl.
  rewrite h0.
  rewrite plus_0_l.
  setoid_rewrite <- (@simple_associativity _ _ mult _ 2 _ _).
  unfold sin, implCR.SinClassCR.
  rewrite  θcorrect.
  fold implCR.SinClassCR.
  autounfold with IRMC.
  unfold cast, Cast_instace_Q_IR, Cart_CR_IR, implCR.SinClassCR, Cart2Polar.
  autorewrite with CRtoIR.
  reflexivity.
Qed.

(* using product rule and:
http://www.math.com/tables/derivatives/more/trig.htm

 (d/dx) tan(x) : sec^2(x) 

To lower bound the quality of the solution found by the optimizer,
we have to upper bound this derivative.
*)

Definition  upwardShiftDeriv :CR :=
let pf :=  (or_intror (extraSpaceX1WValidCosPos _ valid)) in
sqr (// (cos (2 * θ)) ↾ pf) * ('Xs -  (extraSpaceX1W θ))
- (// (cos (2 * θ)) ↾ pf) * (IRasCR (extraSpaceX1Deriv  α cd ('θ))).

(* this can ony be stated after this section is closed *)
Lemma upwardShiftDerivCorrect : 0=(0:CR).
Abort.


End objective.

Require Import CRMisc.numericalOpt.


Definition approxMaximizeUpwardShift : list CR -> option CR :=
  approxMaximize eps CR approxDecideXAdmiss upwardShift.

Require Import MathClasses.interfaces.functors.
Require Import MathClasses.interfaces.monads.
Require Import MathClasses.theory.monads.
Require Import MathClasses.implementations.option.

(* Move and use in approximateAngleAsDegrees.*)
Definition angleAsDegrees (a:CR) : CR :=
 (a*CRPiInv* ('180%positive)).

Let sap : CR -> Q :=  fun r => simpleApproximate r (100)%positive eps.
Definition sidewaysOptimalParamsAndShiftAux (l: list CR) : list CR :=
  match (approxMaximizeUpwardShift l) with
  | None  => [0;0;0;0;0]
  | Some θ => 
    let ds := dStraight θ in
    [(angleAsDegrees θ); upwardShift θ; ds; extraSpaceX1W θ; ds * cos (2*θ)]
  end.

(* Move.*)
Fixpoint NPair (T:Type) (n:nat) : Type :=
match n with
| 0 => void
| 1 => T
| S n => (NPair T n)* T
end.

Definition npair_map {A B:Type} {n:nat} (f:A -> B) (np : NPair A n) : NPair B n.
revert np.
revert n.
fix 1.
intros n np.
destruct n;[exact np|].
specialize (npair_map n).
simpl in *.
destruct n;[exact (f np)|].
destruct np.
exact (npair_map n0, f a).
Defined.

Definition pair_map5 {A B:Type} (f:A -> B) (pa: A * A * A* A * A) : (B * B * B* B * B) :=
 (@npair_map A B 5 f pa).

Definition sidewaysOptimalParamsAndShiftQAux (l: list CR) : (list Q) :=
  List.map  sap (sidewaysOptimalParamsAndShiftAux l).


Definition optimalSidewaysMoveAux (l: list CR) : list (DAtomicMove CR) :=
  match (approxMaximizeUpwardShift l) with
  | None => []
  | Some θ => (sidewaysMoveQCR θ)
  end.

Example approxMaximizeUpwardShiftTest :
  approxMaximizeUpwardShift [] = None.
  reflexivity.
Qed.

Section sampling.
Variable δ: Qpos.

(** the goal here is to create a list of rationals
between 0 and [maxValidAngle] such that any point in that range
is at most δ away from some member of the list.

Thus, the optimal solution, whether real or rational, is also 
at most δ away from a solution in the list that we considered
during the optimization. Because the objective function (upward shift)
is a continuous function with bounded derivative (say ≤ k), the suboptimality 
is at most kδ + eps. Need to characterize k.
 *)

Require Import Qmisc.
Definition maxValidAngleApprox : Q :=
  lowerApprox (compress maxValidAngle) ((QposMake 1 2)*δ).

Definition equiSpacedSamples : list Q :=
  Qmisc.equiSpacedSamples  δ maxValidAngleApprox.

Let samples := (cbvApply (List.map (cast Q CR)) equiSpacedSamples).

Definition optimalSolution : option CR :=
  approxMaximizeUpwardShift samples.

Definition sidewaysOptimalParamsAndShiftQ : (list Q) :=
sidewaysOptimalParamsAndShiftQAux samples.

Definition optimalSidewaysMove : list (DAtomicMove CR) :=
  optimalSidewaysMoveAux samples.

(* Move *)
Lemma preserves_extraSpaceX1DerivUB:
  '(extraSpaceX1DerivUB α cd) = ((extraSpaceX1DerivUB α cd):IR).
Proof using.
  unfold extraSpaceX1DerivUB.
  simpl.
  autounfold with IRMC.
  autorewrite with CRtoIR.
  reflexivity.
Qed.

(* Move *)
Lemma nonneg_extraSpaceX1DerivUB:
 (0:IR) ≤ extraSpaceX1DerivUB α cd.
Proof using.
  apply nonneg_plus_compat;
  [ apply RingLeProp3 | ];apply Cart2DRadNNegIR.
Qed.

Hypothesis δSmallEnough : '`δ ≤ maxValidAngle.

Lemma maxValidAngleApproxNonneg : 0 ≤ maxValidAngleApprox.
Proof using δSmallEnough.
  unfold maxValidAngleApprox.
  apply (order_reflecting (cast Q CR)).
  eapply transitivity;[| apply (proj1 (lowerApproxCorrect _ _))].
  rewrite compress_correct.
  apply flip_le_minus_l.
  rewrite negate_involutive.
  rewrite <- preserves_plus.
  eapply transitivity;[| apply δSmallEnough].
  apply order_preserving;[eauto 2 with typeclass_instances|].
  apply eq_le.
  simpl.
  autounfold with QMC.
  destruct δ; simpl.
  ring.
Qed.

Lemma  equiSpacedSamplesFstValue: 
 {q :Q | List.head  equiSpacedSamples ≡ Some q 
    /\ extraSpaceX1W ('q) ≤ (extraSpaceX1DerivUB α cd) * ('`δ) }.
Proof using δSmallEnough.
  destruct (equiSpacedSamplesFst2 δ maxValidAngleApprox) as [q Hd];
    [apply maxValidAngleApproxNonneg|].
  exists q. destruct Hd as [Hdl Hdr].
  setoid_rewrite Hdl.
  split;[reflexivity|].
  apply CR_leEq_as_IR.
  unfold extraSpaceX1W.
  rewrite compress_correct.
  rewrite preserves_extraSpaceX1.
  rewrite CR_mult_asIR.
  rewrite preserves_extraSpaceX1DerivUB.
  eapply transitivity;
    [apply extraSpaceX10UB|].
- unfold cast, Cast_instace_Q_IR, Cart_CR_IR, implCR.SinClassCR, Cart2Polar.
  autorewrite with CRtoIR.
  apply preserves_nonneg; tauto.

- fold Mult_instance_IR.
  fold (@mult IR _).
  pose proof nonneg_extraSpaceX1DerivUB.
  apply order_preserving; [eauto 2 with typeclass_instances |].
  unfold cast, Cast_instace_Q_IR, Cart_CR_IR, implCR.SinClassCR, Cart2Polar.
  autorewrite with CRtoIR.
  apply order_preserving; [eauto 2 with typeclass_instances |].
  apply Hdr.
Qed.

Lemma  equiSpacedSamplesFstAdmissible: 
(extraSpaceX1DerivUB α cd) * ('`δ) + '(2*`eps) <  'Xs
→
{q :Q | List.head  equiSpacedSamples ≡ Some q 
    /\ approxDecideXAdmiss ('q) ≡ true}.
Proof using δSmallEnough.
  intro H.
  destruct equiSpacedSamplesFstValue as [q Hd].
  exists q. repnd.
  rewrite Hdl.
  split;[reflexivity|].
  unfold approxDecideXAdmiss.
  apply approxDecLtRQApproxComplete.
  eapply le_lt_trans;[apply Hdr|].
  rewrite preserves_minus.
  apply flip_lt_minus_l.
  rewrite negate_involutive.
  assumption.
Qed.

Lemma optimalSolution_isSome :
(extraSpaceX1DerivUB α cd) * ('`δ) + '(2*`eps) <  'Xs
→
   ∃ (m : Q),
      In m equiSpacedSamples
      ∧ approxDecideXAdmiss ('m) ≡ true
      ∧ optimalSolution ≡ Some ('m).
Proof using δSmallEnough.
  intro Hyp.
  destruct (equiSpacedSamplesFstAdmissible Hyp) as [q Hd].
  repnd.
  eapply (approxMaximizeCorrect eps CR approxDecideXAdmiss 
      upwardShift _ ((List.map (cast Q CR) equiSpacedSamples))) in Hdr;
  [| destruct equiSpacedSamples;inversion Hdl; subst; left; reflexivity].
  destruct Hdr as [mr Hs].
  repnd.
  apply in_map_iff in Hsl.
  destruct Hsl as [mq Hsl].
  exists mq.
  split;[tauto|].
  repnd.
  subst mr.
  tauto.
Qed.


End sampling.


End InverseProblem.

Section TestSetup.


Let cd : CarDimensions Q := '(carDim Mazda3Sedan2014sGT).

Let ntriv : nonTrivialCarDim cd.
  unfold nonTrivialCarDim. compute; dands; reflexivity.
Defined. (*Qed? *)

(** all turns will be executed at maximum curvature, which
corresponds to the minimum turn radius allowed by the car's geometry*)
Let α : Q.
  let t := eval compute in (Qinv (minTR Mazda3Sedan2014sGT)) in 
  exact t.
Defined.


(*
Print α.
α := (1 # 150)%Q : Q]
*)

Let αPosQ : (0 < α).
compute. reflexivity.
Defined.

Let turnCentreOut : (width cd <= Qinv α)%Q.
compute. intros H; discriminate.
Defined.  (*Qed? *)

Let eps : Qpos.
  let t := eval compute in ((Qmake 1 100)) in 
  exists t.
  compute. reflexivity.
Defined.

(** extra available space in the X direction.
set to one tenth of the length of the car 
Let Xs : Q.
  let t := eval compute in ((Qmake 1 10) * (totalLength cd)) in 
  exact t.
Defined.

(*
Print Xs.
(178 # 10)%Q 

unit : inches
*)

Let Xsp : (0 < Xs).
compute. reflexivity.
Defined.  (*Qed? *)

Let tapproxMaximizeUpwardShift : list CR → option CR :=
  approxMaximizeUpwardShift cd ntriv α αPosQ turnCentreOut Xs Xsp eps.

Let test1 : option CR :=
(tapproxMaximizeUpwardShift [' (Qmake 1 100); ' (Qmake 1 200)]).
*)

Let approx : option CR -> option Q :=
  sfmap (fun r => approximate r eps).

(* unit : radians. pi radians = 180 degrees. 1 radian ~ 57 degrees *)
Definition δ :Qpos := QposMake 1 100.

Let  tr :Q := '(minTR Mazda3Sedan2014sGT).

Eval compute in tr.

Eval vm_compute in (R2ZApprox (rad ('(βPlusFront cd α)))  eps).
(*235*)
Eval vm_compute in (lengthFront cd).
(*142.
If there is sufficient space at the bottom and if there is more than
235-142 = 93 inches of space in the front, parallel parking can be done in 1 move
*)
Eval vm_compute in (R2ZApprox (spaceNeededFor1MoveSoln cd α)  eps).
(* 93 *)

Definition samples : list Q:= 
equiSpacedSamples cd α δ.

Eval vm_compute in (samples).


Definition optimalSidewaysMoveShiftMazdaQp (Xspos : Qpos ): (list Q) :=
  let (Xs, Xsp) := Xspos in
  (sidewaysOptimalParamsAndShiftQ cd ntriv α αPosQ turnCentreOut Xs Xsp eps δ).

Definition optimalSidewaysMoveMazda (Xspos : Qpos ) : list (DAtomicMove CR) :=
  let (Xs, Xsp) := Xspos in
  optimalSidewaysMove cd ntriv α αPosQ turnCentreOut Xs Xsp eps δ.


Definition optimalSidewaysMoveShiftMazdaQ (q : Q): (list Q) :=
let (Xs, Xsp) := Qpossec.QabsQpos q in
  (sidewaysOptimalParamsAndShiftQ cd ntriv α αPosQ turnCentreOut Xs Xsp eps δ).


Let  tupwardShift (Xspos : Qpos ) : CR -> CR :=
  let (Xs, Xsp) := Xspos in
    upwardShift cd ntriv α αPosQ turnCentreOut Xs Xsp.


Example xxxx :
(optimalSidewaysMoveShiftMazdaQ (QposMake 17 1))
≡ [(171 # 100)%Q; (56 # 100)%Q; (938 # 100)%Q; (764 # 100)%Q; (936 # 100)%Q].
(*vm_compute.
reflexivity. *)
Abort.


Definition xspaceSamples (np : positive ): list Q := 
let max :Q  := (approximate (spaceNeededFor1MoveSoln cd α) eps) in
let eqs : list Q := equiMidPoints np in
  List.map (mult max) eqs.

Definition plotl `(f: A->B) (l: list A) : (list (A * B)) :=
List.map (fun a => (a,f a)) l.

(*
Eval vm_compute in 
  (List.map (fun q => approximateQ q (100)%positive)
     (xspaceSamples (100)%positive)).
*)     
Definition plotOptimalSidewaysMoveShiftMazdaQ (np : positive) :=
  plotl optimalSidewaysMoveShiftMazdaQ (xspaceSamples np).

(**
Ideas to make it fast: 
(0.7s (eps=0.01 inch, 41 samples) afer extraction is fast enough for now)
 
1) Switch to AR.

Even though operations on AR are exact, AR is a completion of 
AQ (approximate rationals), where there is no exact division.
This should not be a problem. In worst case, one can inject the AQs
into ARs and then do the exact division in AR.

Does CoRN.reals.fast.Compress, already provide some of the advantages
of AR in CR?

2) It suffices to only consider rational solutions. We are only after
approximate optimality. We can replace [sin] by [rational_sin] ...  e.t.c.
[sin] invokes [rational_sin].

*)


(*
Print boundAbove.
Print QboundAbove_uc.
Print QboundAbove_uc_prf.
SearchAbout boundAbove.
SearchAbout CR Q.
*)

End TestSetup.
