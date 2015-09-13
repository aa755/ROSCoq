
Require Import MathClasses.interfaces.canonical_names.

Require Import ROSCOQ.StdlibMisc.

(*Move the 2 functions below to other file*)


Require Import interfaces.abstract_algebra.
Require Export Coq.Lists.List.

Instance InstanceDecidableEq {T:Type} {deq : DecEq T} (x y:T) : Decision (x ≡ y).
  apply eqdec.
Defined.


Instance InstanceDecidableIn {T:Type} {deq : DecEq T} (h:T) (l: list T) : Decision (In h l).
apply in_dec. apply eqdec.
Defined.

(*
copied from https://github.com/aa755/CFGV/blob/d230d5d0e4d63e49bb80484baed7c630215384ea/list.v#L3140
*)
Instance InstanceDecidableNoDup {T:Type} {deq : DecEq T} (l: list T) : Decision (NoDup l).
induction l; [apply left; constructor|].
  destruct (decide (In a l));[right | ].
  - intro Hin. inversion Hin; auto.
  - destruct IHl; [left; constructor; trivial| right].
    intro Hnt. inversion Hnt; auto.
Defined.
                                 

