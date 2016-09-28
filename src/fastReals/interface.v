(** CoRN has several definitions of constructive reals : IR, CR, AR.
    CR, and then AR was designed to get faster and faster
    computations with reals.
    So, this interface attempts to axiomatize a fast real and common operations on it,
    so that most of our development can be independent of the choice of a fast implementation.
    The [CReal] interface is a nice starting point. It a [CField] with ordering and 
    cauchy limits.
    There is Coq proof that all implementaions of [CReal] are isomorphic.

    However, that interface is not sufficient. 
    Even when one fixes a representation of reals, there are several
    increasingly fast ways of computing functions like sine, cosine, division
    (e.g. [CRinv] vs [CRinvT])
    which show up often in robotic / cyber-physical programs.
    So, we also include such functions, even though they are definable w.r.t [CReals].

    A bureaocratic problem with [CReal] is that it uses the old bundled style
    and not the modern more convenient typeclass based style of MathClasses.
    We use the latter style.

    We will provide implementations using CR and AR.
    It is quite likely that in the future there will be much faster implementations.

    This file is a work in progress.
*)



Class MinClass (A:Type) := min : A -> A -> A.
Class MaxClass (A:Type) := max : A -> A -> A.

(** generalized Sin Class. The domain may be some kind of (approx) rationals *)
Class GSinClass (B  A : Type) := gsin :  B->A.
Class GCosClass (B  A : Type) := gcos :  B->A.

Class SinClass (A:Type) := sin :> GSinClass A A.
Class CosClass (A:Type) := cos :> GCosClass A A.

Class ApartT (A:Type) := apartT: A -> A -> Type.

Require Import MathClasses.interfaces.canonical_names.

(*reciprocal. generalizes [CRinvT], which uses the constructive proof of
apartness during division *)
Class ReciprocalT (A:Type ) `{Zero A} `{ApartT A}
  := recipT: forall (a:A), apartT a 0 -> A.

Definition NonZeroT (A:Type) {_:ApartT A} {_:Zero A}
  := sigT (fun a => apartT a (0:A)).

(* Arguments NonZeroT A {_} {_}. *)


Definition recip1T {A:Type} {_:ApartT A} {_:Zero A} {_ : ReciprocalT A}
  (a: NonZeroT A) := recipT (projT1 a) (projT2 a).

Infix "≭" := apartT (at level 75, no associativity) : mc_scope.


Require Import ROSCOQ.IRMisc.CoRNMisc.
(**because most of the theory of analysis in CoRN is built for IR. These might
be derivable. the following functions are not used yet.*)
Class IsoToIR (A:Type) := isoToIR : A -> IR.
Class IsoFromIR (A:Type) := isoFromIR : IR -> A.

