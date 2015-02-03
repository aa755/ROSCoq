(*  Although angles can be represented as real numbers (CR), 
    the notions of equality and distance would not be appropriate 
    in such a definition. So we wrap up real numbers in a special [Angle] 
    type where equality and distance are right *)

Section Angles.
Require Export IRLemmasAsCR.
(** [CR] is an instance of CReals.
     But [IR] is not declared to be a [Ring] with [order]?
    There is something from 
    CRing to ring_theory and ring_theory to Ring.
    We still need LT.

    [CReals] is is not defined for [AQ]. However, we can define it if we use [AQ]
*)


Context `(R : CReals).
Inductive AngleRad : Type :=
| mkAng : R → AngleRad.

(** first define subtraction which is supposed to be between [-π] and [π]?
    Either way, distance is supposed to be between [0] and [π]. 
    It is a conitnuous function; implementable using min, max etc *)
Definition AngleMS : MetricSpace.
Abort.
End Angles.