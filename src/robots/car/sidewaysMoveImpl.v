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

2 parameters remain : how much to drive while turning,
and how much to drive while moving straight.
The total X-space needed can be decomposed as a sum
of 2 terms, each of which is a function of these 2 parameters. 
The latter function, which
is the X-space consumed by the straight move, is easily
invertible. The former, which is
the space needed to execute the [Wriggle] part of the sideways move,
is a horrendous quartic -- will be solved numerically, and only approximately.
(It may be possible to solve it exatly.)

There is a meta parameter [k] denoting what fraction of the available
X-space is spent on doing Wriggle. The upward shift (the larger, the better) 
is 0 for both extremes of this paremeter (0 and 1).
If wriggle is done without consuming any extra space, no turn will
be produced, and hence the straight move in the middle will result
in  0 upward shift. On the other hand, if all the space 
is spent on wriggle, the
car will turn a lot, but return to its original position
 (Wriggle + WriggleInv == 0).
We will try many choices of this [k], and pick the best among those.

The proof only says that the sideways move will be safe, and
produce a positive upward shift. Depending on how carefully the
parameter [k] is chosen, a possibly approximate optimality theorem
may be proven.
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


Let d'  : CR := (compress cos2θ_inv) * ('Xs -  (extraSpaceX1W θ)).

Require Import MathClasses.theory.fields.



Let d :CR := ('tr*θ).
Let sidewaysMove : list DAtomicMove 
  := SidewaysAux ('α) αNZ ('d) ('(d')).

Lemma  θcorrect : θ = 'α * d.
Proof using αPosQ.
  subst d.
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
Lemma upwardShiftDerivCorrect : 0=0.
Abort.


End objective.

Require Import CRMisc.numericalOpt.


Definition approxMaximizeUpwardShift : list CR -> option CR :=
  approxMaximize eps CR approxDecideXAdmiss upwardShift.

Example approxMaximizeUpwardShiftTest :
approxMaximizeUpwardShift [] = None.
reflexivity.
Qed.



Locate Qpos.

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

Definition optimalSolution : option CR :=
  approxMaximizeUpwardShift 
    (List.map (cast Q CR) equiSpacedSamples).

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

Hypothesis δLargeEnough : '`δ ≤ maxValidAngle.

Lemma maxValidAngleApproxNonneg : 0 ≤ maxValidAngleApprox.
Proof using δLargeEnough.
  unfold maxValidAngleApprox.
  apply (order_reflecting (cast Q CR)).
  eapply transitivity;[| apply (proj1 (lowerApproxCorrect _ _))].
  rewrite compress_correct.
  apply flip_le_minus_l.
  rewrite negate_involutive.
  rewrite <- preserves_plus.
  eapply transitivity;[| apply δLargeEnough].
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
Proof using δLargeEnough.
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
Proof using δLargeEnough.
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
Proof using δLargeEnough.
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

(** extra available space in the X direction.
set to one tenth of the length of the car *)
Let Xs : Q.
  let t := eval compute in ((Qmake 1 10) * (totalLength cd)) in 
  exact t.
Defined.

(*
Print Xs.
(172 # 10)%Q 

unit : inches
*)

Let Xsp : (0 < Xs).
compute. reflexivity.
Defined.  (*Qed? *)

Let eps : Qpos.
  let t := eval compute in ((Qmake 1 100)) in 
  exists t.
  compute. reflexivity.
Defined.

Let tapproxMaximizeUpwardShift : list CR → option CR :=
approxMaximizeUpwardShift cd ntriv α αPosQ turnCentreOut Xs Xsp eps.

Let test1 : option CR :=
(tapproxMaximizeUpwardShift [' (Qmake 1 100); ' (Qmake 1 200)]).

Let approx : option CR -> option Q :=
option_map (fun r => approximate r (QposMake 1 10)).

(* unit : radians. pi radians = 180 degrees. 1 radian ~ 57 degrees *)
Definition δ :Qpos := QposMake 1 100.

Definition samples : list Q:= 
equiSpacedSamples cd α δ.

Eval vm_compute in (samples).


Eval vm_compute in (length samples, eps).
Example dshffkldjs:
(approx (optimalSolution cd ntriv α αPosQ turnCentreOut Xs Xsp eps δ)) =
(Some (131196 # 3288200)%Q).
(* this is the 5^th member member of the list [samples] of 41 elements.
The tests below confirm that the maxima is indeed achieved close to that point.
*)
Proof using.
time vm_compute.
(* Tactic call ran for 90.473 secs (90.508u,0.056s) *)
reflexivity.
Abort.

Let  tupwardShift : CR -> CR
:= upwardShift cd ntriv α αPosQ turnCentreOut Xs Xsp.

(* quality of the computed soultion *)
Example exampleUpw : 
approximate (compress (tupwardShift ('((131196 # 3288200)%Q))))
            (QposMake 1 100) 
≡ (130 # 201)%Q.
vm_compute.
reflexivity.
Abort.

Example exampleUp2 : 
approximate (compress (tupwardShift ('((231196 # 3288200)%Q))))
            (QposMake 1 100) 
≡ (42 # 201)%Q.
vm_compute.
reflexivity.
Abort.

Example exampleUp2 : 
approximate (compress (tupwardShift ('((031196 # 3288200)%Q))))
            (QposMake 1 100) 
≡ (57 # 201)%Q.
vm_compute.
reflexivity.
Abort.

Example exampleUp2 : 
approximate (compress (tupwardShift ('((111196 # 3288200)%Q))))
            (QposMake 1 100) 
≡ (128 # 201)%Q.
vm_compute.
reflexivity.
Abort.

Example exampleUp2 : 
approximate (compress (tupwardShift ('((137196 # 3288200)%Q))))
            (QposMake 1 100) 
≡ (129 # 201)%Q.
vm_compute.
reflexivity.
Abort.

Eval vm_compute in samples.
Example exampleUp2 : 
approximate (compress (tupwardShift ('(((32799 # 80200))%Q))))
            (QposMake 1 100) 
≡ (-9120 # 201)%Q.
vm_compute.
reflexivity.
Abort.

Eval vm_compute in (samples).


(**
Ideas to make it fast:
 
1) Switch to AR.

Even though operations on AR are exact, AR is a completion of 
AQ (approximate rationals), where there is no exact division.
This should not be a problem. In worst case, one can inject the AQs
into ARs and then do the exact division in AR.

Does CoRN.reals.fast.Compress, already provide some of the advantages
of AR in CR?


2) extract it to OCaml or Haskell. There is a chance that the bloat of proof
is slowing things down. Also vm_compute use machine (big) integers instead of Coq's
binary Z?

3) It suffices to only consider rational solutions. We are only after
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

