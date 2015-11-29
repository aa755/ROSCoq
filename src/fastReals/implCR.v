Require Export interface.
Require Import CoRN.reals.fast.CRtrans.

Global Instance MinClassCR : MinClass CR := fun x y => CRmin x y.
Global Instance MaxClassCR : MaxClass CR := fun x y => CRmax x y.
Global Instance SinClassCR : SinClass CR := sin.
Global Instance CosClassCR : CosClass CR := cos.
