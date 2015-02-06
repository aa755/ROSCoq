Require Import IRMisc.ContField.

Set Implicit Arguments.
Require Import Coq.Unicode.Utf8.


Section ContFAlgebra.
Require Import CRMisc.IRLemmasAsCR.

Open Scope uc_scope.
Definition toPart (f : (CR --> CR)) : PartIR.
  apply Build_PartFunct with (pfdom := (realline)) 
    (pfpfun := fun ir pp => CRasIR (f (IRasCR ir))).
  - apply iprop_wd.
  - intros ? ? ? ?. admit.
Defined.

End ContFAlgebra.

