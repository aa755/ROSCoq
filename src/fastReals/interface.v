(** CoRN has several definitions of constructive reals : IR, CR, AR.
    CR, and then, AR was designed to get faster computations with reals.
    So, this interface attempts to axiomatize a fast real and common operations on it,
    so that most of our development can be independent of the choice of a fast implementation.
    The [CReal] interface is a nice starting point. It a [CField] with ordering and 
    cauchy limits.
    There is Coq proof that all implementaions of [CReal] are isomorphic.
    This isomorphism can be used to prove axiomatic properties by
    computing with an fast implementation.

    However, that interface is not sufficient. 
    Even when one fixes a representation of reals, there are several
    increasingly fast ways of computing functions like sine, cosine,
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
Class SinClass (A:Type) := sin : A -> A.
Class CosClass (A:Type) := cos : A -> A.

Require Import ROSCOQ.IRMisc.CoRNMisc.
(**because most of the theory of analysis in CoRN is built for IR. These might
be derivable*)
Class IsoToIR (A:Type) := isoToIR : A -> IR.
Class IsoFromIR (A:Type) := isoFromIR : IR -> A.

