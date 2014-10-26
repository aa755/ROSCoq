
Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export CoRN.ftc.Derivative.   
Require Export CoRN.ftc.Integral.
Require Export CoRN.ftc.FTC.


Lemma inDomDerLeft : 
forall {F F': PartFunct IR} {a b : IR} {Hab : a[<]b},
Derivative_I Hab F F'
-> (Dom F a).
Proof.
  intros ? ? ? ? ?  der.
  apply derivative_imp_inc in der.
  apply der. unfold compact. split.
  - apply leEq_reflexive.
  - apply less_leEq. trivial.
Defined.

Lemma inDomDerRight : 
forall {F F': PartFunct IR} {a b : IR} {Hab : a[<]b},
Derivative_I Hab F F'
-> (Dom F b).
Proof.
  intros ? ? ? ? ?  der.
  apply derivative_imp_inc in der.
  apply der. unfold compact. split.
  - apply less_leEq. trivial.
  - apply leEq_reflexive.
Defined.

Lemma AntiderivativeUB : 
forall (F F': PartFunct IR) (a b : IR) (Hab : a[<]b)
     (derivF : Derivative_I Hab F F') (c : IR),
     let HabC := (less_leEq IR a b Hab) in
     let Hdb := (inDomDerRight derivF) in
     let Hda := (inDomDerLeft derivF) in
     fun_lub_IR F' (Compact HabC) c
     -> (F b Hdb[-] F a Hda)[<=]c[*](b[-]a).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? Hlub.
  subst Hda. subst Hdb.
  unfold inDomDerRight.
  unfold inDomDerLeft.
  rewrite <- Barrow.