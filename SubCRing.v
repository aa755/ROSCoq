Require Export CoRN.algebra.CRings.
Section SubRing.

Variable A : CRing.
Variable AProp : A -> Type.

Definition SubCSetoid := Build_SubCSetoid  A AProp.

