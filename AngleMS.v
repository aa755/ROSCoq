(*  Although angles can be represented as real numbers (CR), 
    the notions of equality and distance would not be appropriate 
    in such a definition. So we wrap up real numbers in a special [Angle] 
    type where equality and distance are right *)

Section Angles.
Require Export CRMisc.IRLemmasAsCR.
(** [CR] is an instance of CReals.
     But [IR] is not declared to be a [Ring] with [order]?
    There is something from 
    CRing to ring_theory and ring_theory to Ring.
    We still need LT.
    [CReals] is is not defined for [AQ]. However, we can define it if we use [AQ]

    Since it really matters to make it fast on CR and not so much for CR,
    lets define it for CR and use CRasIR for IR?

   onenote:https://d.docs.live.net/946e75b47b19a3b5/Documents/PhD5/Submissions/ConHyb.one#(computable)%20metric%20space%20on%20angles&section-id={10FE6329-81C9-4025-AD71-4FC8EFC3BB57}&page-id={339A76CB-9539-4EAC-BF93-B3AD40D7818B}&end
*)


Inductive AngleRad : Type :=
| mkAng : CR → AngleRad.

Definition angleValue (a : AngleRad) : CR :=
match a with
| mkAng x => x
end.

Coercion angleValue : AngleRad >-> st_car.

(** first define subtraction which is supposed to be between [-π] and [π]?
    Either way, distance is supposed to be between [0] and [π]. 
    It is a conitnuous function; implementable using min, max etc *)

(** Distance of an angle from 0 radians.
    approximate it to some integel multiple of [π/2] and then do induction
    on the integer *)
Definition AngleRadNorm (ang : CR) : CR.
Admitted.

Require Import StdlibMisc.
Lemma AngleRadNormCorrect : ∀ (a : CR),
    (AngleRadNorm a ≤ π) × {k : Z | (CRabs (a + π*('(2*k)%Q)) = AngleRadNorm a)}.
Admitted.


Instance Norm_instance_Angle : NormSpace AngleRad CR :=
   AngleRadNorm ∘ angleValue.


Definition AngleMS : MetricSpace.
Abort.
End Angles.
