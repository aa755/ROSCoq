Require Import geometry2D.
Require Import Vector.
Require Import fastReals.misc.
Require Import MCInstances.
Require Import fastReals.interface.

Open Scope mc_scope.


Lemma Min_plusl: ∀ a b c : ℝ, min (c + a) (c + b) =  c + min a b.
Proof.
  intros.
  rewrite (plus_comm c).
  rewrite (plus_comm c).
  setoid_rewrite Min_plus.
  rewrite (plus_comm c).
  reflexivity.
Qed.

Lemma Max_plusl: ∀ a b c : ℝ, max (c + a) (c + b) =  c + max a b.
Proof.
  intros.
  rewrite (plus_comm c).
  rewrite (plus_comm c).
  setoid_rewrite max_plus.
  rewrite (plus_comm c).
  reflexivity.
Qed.

Lemma minCartSum : forall c a b : Cart2D IR,
  minCart (c+a) (c+b) = c + minCart a b.
Proof.
  intros. unfold minCart. simpl.
  rewrite Min_plusl.
  rewrite Min_plusl.
  split; reflexivity.
Qed.

Lemma maxCartSum : forall c a b : Cart2D IR,
  maxCart (c+a) (c+b) = c + maxCart a b.
Proof.
  intros. unfold maxCart. simpl.
  rewrite Max_plusl.
  rewrite Max_plusl.
  split; reflexivity.
Qed.

Global Instance ProperMinCart : 
  Proper (equiv ==> equiv  ==> equiv) (@minCart IR _).
Proof.
  intros ? ? h1  ? ? h2.
  destruct h1. destruct h2.
  split; simpl; apply Max_AbsIR.Min_wd_unfolded; tauto.
Qed.

Global Instance ProperMaxCart : 
  Proper (equiv ==> equiv  ==> equiv) (@maxCart IR _).
Proof.
  intros ? ? h1  ? ? h2.
  destruct h1. destruct h2.
  split; simpl; apply Max_AbsIR.Max_wd_unfolded; tauto.
Qed.

Global Instance AssociativeMinIR : `{Associative  (@min IR _)}.
  intros ? ? ?. apply MinAssoc.
Qed.

Global Instance AssociativeMaxIR : `{Associative  (@max IR _)}.
  intros ? ? ?. apply MaxAssoc.
Qed.

Global Instance AssociativeMinCart `{MinClass R} `{Associative _ (@min R _)}: 
  Associative  (@minCart R _).
Proof.
  intros ? ? ?. split; simpl;
  apply simple_associativity.
Qed.

Global Instance AssociativeMaxCart `{MaxClass R} `{Associative _ (@max R _)}: 
  Associative  (@maxCart R _).
Proof.
  intros ? ? ?. split; simpl;
  apply simple_associativity.
Qed.

Global Instance CommutativeMinIR : `{Commutative  (@min IR _)}.
  intros ? ?. apply Min_comm.
Qed.

Global Instance CommutativeMaxIR : `{Commutative  (@max IR _)}.
  intros ? ?. apply Max_comm.
Qed.

Global Instance CommutativeMinCart `{MinClass R} `{Commutative _ _ (@min R _)}: 
  Commutative  (@minCart R _).
Proof.
  intros ? ?. split; simpl;
  apply commutativity.
Qed.

Global Instance CommutativeMaxCart `{MaxClass R} `{Commutative _ _ (@max R _)}: 
  Commutative  (@maxCart R _).
Proof.
  intros ? ?. split; simpl;
  apply commutativity.
Qed.

Hint Unfold cos CosClassIR sin SinClassIR min MinClassIR max MaxClassIR: IRMC.

Require Import IRTrig.
Lemma unitVecNonNeg : forall θ, 0 ≤ θ ≤ (½ * π)
  -> 0 ≤ unitVec θ.
Proof.
  intros ? hh.
  pose proof (less_leEq ℝ [0] Pi pos_Pi) as h.
  apply nonneg_div_two' in h.
  autounfold with IRMC in hh.
  unfold Zero_instance_IR in hh.
  destruct hh as [x y]. 
  rewrite PiBy2DesugarIR in y.
  pose proof MinusPiBy2Le0.
  split; simpl;
  [apply Cos_nonneg | apply Sin_nonneg]; eauto 3 with CoRN.
Qed.

  Lemma unitVec90Minus :  ∀ θ:IR, 
    unitVec (½ * π - θ) = {|X:= sin θ; Y:= cos θ|}.
  Proof using.
    intros ?. split; simpl;
    autounfold with IRMC.
    -  rewrite PiBy2DesugarIR.
      apply Cos_HalfPi_minus.
    - rewrite PiBy2DesugarIR.
      apply Sin_HalfPi_minus.
  Qed.

Local Opaque Sin.
Local Opaque Cos.

  Lemma unitVecMinus90 :  ∀ θ:IR, 
    unitVec (θ - ½ * π) = {|X:= sin θ; Y:=- cos θ|}.
  Proof using.
    intros ?. unfold EquivCart, unitVec.
    autounfold with IRMC. simpl.
    rewrite <- Cos_inv.
    setoid_rewrite minusInvR.
    rewrite <- (cg_inv_inv _ (Sin (θ [+] [--] (½ [*] π)))).
    rewrite <- Sin_inv.
    setoid_rewrite minusInvR.
    split.
    - rewrite PiBy2DesugarIR.
      apply Cos_HalfPi_minus.
    - rewrite PiBy2DesugarIR.
      apply cg_inv_wd.
      apply Sin_HalfPi_minus.
  Qed.


Lemma unitVecMinDistr :  forall θ a b:IR, 0 ≤ θ ≤ (½ * π)
  ->
  minCart ((unitVec θ) * 'a) ((unitVec θ) * 'b)
     = (unitVec θ) * '(min a b).
Proof.
  intros ? ? ? hh.
  apply unitVecNonNeg in hh. unfold unitVec in hh.
  destruct hh as [x y]. simpl in x, y. 
  unfold minCart. split; simpl;
  autounfold with IRMC;
  rewrite MinMultLeft; try reflexivity; try assumption.
Qed.


Lemma unitVecMaxDistr :  forall θ a b:IR, 0 ≤ θ ≤ (½ * π)
  ->
  maxCart ((unitVec θ) * 'a) ((unitVec θ) * 'b)
     = (unitVec θ) * '(max a b).
Proof.
  intros ? ? ? hh.
  apply unitVecNonNeg in hh. unfold unitVec in hh.
  destruct hh as [x y]. simpl in x, y. 
  unfold maxCart. split; simpl;
  autounfold with IRMC;
  rewrite MaxMultLeft; try reflexivity; try assumption.
Qed.

Lemma minCart_leEq_lft: ∀ x y : Cart2D ℝ, 
  minCart x y ≤ x.
Proof using .
  intros ? ?.
  split; apply Min_leEq_lft.
Qed.

Lemma minCart_leEq_rht: ∀ x y : Cart2D ℝ, 
  minCart x y ≤ y.
Proof using .
  intros ? ?. rewrite commutativity.
  apply minCart_leEq_lft.
Qed.

Lemma lft_leEq_maxCart: ∀ x y : Cart2D ℝ, 
  x ≤ maxCart x y.
Proof using .
  intros ? ?.
  split; apply lft_leEq_Max.
Qed.

Lemma rht_leEq_maxCart: ∀ x y : Cart2D ℝ, 
  y ≤ maxCart x y.
Proof using .
  intros ? ?. rewrite commutativity.
  apply lft_leEq_maxCart.
Qed.

Lemma leEq_minCart : ∀ x y z : Cart2D ℝ, 
  z ≤ x → z ≤ y → z ≤ minCart x y.
Proof using .
  intros ? ? ? Hab Hbc.
  destruct Hab, Hbc.
  split; apply leEq_Min; assumption.
Qed.

Lemma maxCart_leEq : ∀ x y z : Cart2D ℝ, 
  x ≤ z → y ≤ z → maxCart x y ≤ z.
Proof using .
  intros ? ? ? Hab Hbc.
  destruct Hab, Hbc.
  split; apply Max_leEq; assumption.
Qed.

  
Hint Resolve minCart_leEq_lft
minCart_leEq_rht
lft_leEq_maxCart
rht_leEq_maxCart
leEq_minCart
maxCart_leEq
 : MinMaxCart.

Lemma boundingUnionIff: forall (a b c : Line2D IR),
  boundingUnion a b ⊆ c
  <-> (a ⊆ c /\ b ⊆ c).
Proof using .
  intros. unfold boundingUnion, le, LeAsSubset.
  simpl. split; intro hh.
  - repnd. split; split;
    eapply (@transitivity (Cart2D ℝ) le _);
    try apply hhl;
    try apply hhr;
    eauto using
      minCart_leEq_lft,
      minCart_leEq_rht,
      lft_leEq_maxCart,
      rht_leEq_maxCart.
  - repnd. split; eauto using 
      leEq_minCart, maxCart_leEq.
Qed.

Global Instance CommBoundingUnion `{e:Equiv R} `{m:MinClass R}
`{M: MaxClass R} `{@Commutative R e R min} `{@Commutative R e R max}:
  Commutative boundingUnion.
Proof using.
  unfold BoundingRectangle. intros ? ?. split; simpl.
  - apply CommutativeMinCart.
  - apply CommutativeMaxCart.
Qed.

Lemma boundingUnionPlus : forall (a b c: Line2D IR),
  boundingUnion (b + a) (b + c)
  = b + (boundingUnion a c).
Proof using.
  intros ? ? ?.
  unfold boundingUnion.
  simpl.
  rewrite minCartSum.
  rewrite maxCartSum.
  reflexivity.
Qed.

Lemma  boundingUnionLeft:
  ∀ a b: Line2D ℝ, a ⊆ boundingUnion a b.
Proof.
  intros ? ?. unfold boundingUnion;
  split; simpl; eauto using minCart_leEq_lft,
    lft_leEq_maxCart.
Qed.

Lemma  boundingUnionRight:
  ∀ a b: Line2D ℝ, b ⊆ boundingUnion a b.
Proof.
  intros. rewrite commutativity.
  apply boundingUnionLeft.
Qed.

Global Instance ProperboundingUnion:
 Proper (equiv ==> equiv ==> equiv) 
 (@boundingUnion IR _ _).
Proof.
  intros ? ? H1 ? ? H2.
  unfold boundingUnion.
  rewrite H1, H2. reflexivity.
Qed.

Ltac remCart2D c1min :=
  match goal with
    [|- context [{|
            X :=?x ; Y :=?y|} ]] 
         => remember ({|
            X :=x ; Y :=y|}) as c1min
    end.

Require Import MCMisc.tactics.
Ltac simpRemCart2D c1min Heqc1min :=
  match goal with
    [|- context [{|
            X :=?x ; Y :=?y|} ]] 
         => mcremember ({|
            X :=x ; Y :=y|}) c1min Heqc1min;
          ring_simplify x in Heqc1min; 
          ring_simplify y in Heqc1min
    end.

Definition unitVecT `{SinClass R} `{CosClass R} (t:R) := transpose (unitVec t).

Definition flipAngle (c:Polar2D IR) : Polar2D IR:=
{| rad := rad c ; θ:= ½ * π -θ c|}.


Lemma minCartIsLeft : forall (a b : Cart2D IR),
  a ≤ b
  -> minCart a b = a.
Proof using.
  intros ? ? Hle.
  destruct Hle.
  split; simpl; apply leEq_imp_Min_is_lft; assumption.
Qed.

Lemma maxCartIsRight : forall (a b : Cart2D IR),
  a ≤ b
  -> maxCart a b = b.
Proof using.
  intros ? ? Hle.
  destruct Hle.
  split; simpl; apply leEq_imp_Max_is_rht; assumption.
Qed.

Require Import MCMisc.rings.

  Local Notation ConfineRect := (Line2D).
  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).

Lemma unionWithNonNegDisplacement : forall (a: ConfineRect IR) (d : Cart2D IR),
  0 ≤ d
  -> boundingUnion a (a+'d)
    = {| minxy := lstart a ; maxxy := lend a + d |}.
Proof using.
  intros ? ? Hle.
  split; simpl.
  - rewrite minCartIsLeft; auto.
    rewrite commutativity.
    apply RingLeProp1. assumption.
  - rewrite maxCartIsRight; auto.
    rewrite commutativity.
    apply RingLeProp1. assumption.
Qed.

Require Import MathClasses.interfaces.vectorspace.

Require Import IRMisc.LegacyIRRing.

Require Import CartIR.
(* Move *)
Lemma FFT2 : forall (θ:IR),
(Cos θ * Cos θ + Sin θ * Sin θ) = 1.
Proof using.
  intro.
  rewrite <- (FFT θ).
  simpl.
  IRring.
Qed.

Require Import fastReals.interface.

Lemma FFT3 : forall (θ:IR),
cos θ * cos θ  = 1 - sin θ * sin θ.
Proof using.
  intro.
  rewrite <- (FFT θ).
  simpl.
  IRring.
Qed.

Definition negY `{One A}`{Negate A} : Cart2D A:= 
{|X:=1;Y:=-1|}.

Lemma unitVNegate :
  forall (β : IR), unitVec (- β) = negY * unitVec β.
Proof using.
  intros.
  split; simpl.
  - rewrite mult_1_l. apply Cos_inv.
  - rewrite <- negate_mult_distr_l.
    rewrite mult_1_l. apply Sin_inv.
Qed.



Lemma rotateAxisInvSimpl :
forall (p : Cart2D IR) (θ:IR),
(rotateAxis (-θ) p) =   
  {| X := X p * cos θ - Y p * sin θ;
    Y := Y p * cos θ + X p * sin θ
  |}.
Proof using.
  intros ? ?.  unfold rotateAxis. simpl.
  unfold inprod, InProductCart2D.
  split; simpl; 
  autounfold with IRMC;
  rewrite Cos_inv;
  rewrite Sin_inv; ring.
Qed.  
  
Lemma rotateAxisInvertibleIR :
forall (p : Cart2D IR) (θ:IR),
(rotateAxis (-θ)) ((rotateAxis θ) p) = p.
Proof using.
  intros ? ?. rewrite rotateAxisInvSimpl.
  unfold rotateAxis, inprod, InProductCart2D.
  split; simpl;
  autounfold with IRMC;
  ring_simplify.
  - setoid_rewrite <- (mult_1_r (X p)) at 3.
    rewrite <- (FFT θ).
    simpl. IRring.
  - setoid_rewrite <- (mult_1_r (Y p)) at 3.
    rewrite <- (FFT θ).
    simpl. IRring.
Qed.

Lemma nflipAsTranspose  `{Ring R} : forall (p : Cart2D R),
  nflip p = negY * transpose p.
Proof using.
  intros ?.
  split; simpl.
  - symmetry. apply mult_1_l.
  - rewrite <- negate_mult_distr_l.
    rewrite mult_1_l. reflexivity.
Qed.

Lemma nflipNegY `{Ring R} : forall (p : Cart2D R),
  nflip (negY * p) =  - transpose p.
Proof using.
  intros ?.
  split; simpl.
  - rewrite <- negate_mult_distr_l.
    rewrite mult_1_l. reflexivity.
  - symmetry. rewrite mult_1_l. reflexivity.
Qed.


Lemma multDotLeft `{Ring A}:
  ∀ (a:A) (b c : Cart2D A), a * (⟨ b, c ⟩) = ⟨ ' a * b, c ⟩.
Proof using.
  intros. unfold inprod, InProductCart2D.
  simpl.
  do 2 rewrite <- (@simple_associativity _ _ mult _ _).
  rewrite <- plus_mult_distr_l.
  reflexivity.
Qed.

Definition totalSpaceX (c : ConfineRect IR) :IR :=
  X (maxxy c) - X (minxy c).
