Require Import fastReals.interface.
Require Import Coq.ZArith.BinInt.

(*Coq.Numbers.BinNums.*)
Global Instance MinClassZ : MinClass Z := Zmin.
Global Instance MaxClassZ : MaxClass Z := Zmax.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.

Require Import ROSCOQ.core.
Require Import CoRN.reals.fast.CRtrans.

Global Instance MinClassIR : MinClass IR := Min.
Global Instance MaxClassIR : MaxClass IR := Max.
Global Instance SinClassIR : SinClass IR := Sin.
Global Instance CosClassIR : CosClass IR := Cos.

Require Import MathClasses.interfaces.abstract_algebra.

Global Instance srmInjQ : SemiRing_Morphism (cast Q IR).
Proof using.
repeat (split; try apply _).
- intros. apply inj_Q_plus.
- intros. apply inj_Q_Zero.
- intros. apply inj_Q_mult.
- intros. apply inj_Q_One.
Qed.


Require Import MathClasses.theory.rings.
(*typeclass resolution happens right here, when declaring the database,
and not while rewriting. leaving out arguments here can confuse
the resolution later*)
Hint Rewrite  
(@preserves_2 Q IR _ _ _ _ _ _ _ _ _ _ (@cast Q IR _) _)
(@preserves_1 Q IR _ _ _ _ _ _ _ _ _ _ (@cast Q IR _) _) 
(@preserves_0 Q IR _ _ _ _ _ _ _ _ _ _ (@cast Q IR _) _) 
(@preserves_negate Q _ _ _ _ _ _ _ IR _ _ _ _ _ _ _  (@cast Q IR _) _)
(@preserves_plus Q IR _ _ _ _ _ _ _ _ _ _ (@cast Q IR _) _)
(@preserves_mult Q IR  _ _ _ _ _ _ _ _ _ _ (@cast Q IR _) _)
 : Q2RMC.

Require Import MathClasses.interfaces.orders.

Global Instance OrderPreservingQR : OrderPreserving (cast Q ℝ).
Proof using.
  split;[split; try apply _|].
  intros ? ? H. apply inj_Q_leEq. exact H.
Qed.

Hint Unfold cos CosClassIR sin SinClassIR min MinClassIR max MaxClassIR One_instance_IR: IRMC.


