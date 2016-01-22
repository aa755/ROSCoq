Require Export interface.
Require Import CoRN.reals.fast.CRtrans.

Global Instance MinClassCR : MinClass CR := fun x y => CRmin x y.
Global Instance MaxClassCR : MaxClass CR := fun x y => CRmax x y.
Global Instance SinClassCR : SinClass CR := sin.
Global Instance CosClassCR : CosClass CR := cos.
Global Instance SinClassQCR : GSinClass Q CR := rational_sin.
Global Instance CosClassQCR : GCosClass Q CR := rational_cos.

Global Instance ApartTCR : ApartT CR := CRapartT.

Global Instance RecipTCR : @ReciprocalT CR _ _ := CRinvT.

Require Import CartCR.
Require Import Vector.
Global Instance Cart2PolarCR : Cast (Cart2D Q) (Polar2D CR) := Cart2Polar.
