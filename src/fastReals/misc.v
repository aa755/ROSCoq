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


Hint Unfold cos CosClassIR sin SinClassIR min MinClassIR max MaxClassIR One_instance_IR: IRMC.


