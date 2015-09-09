Require Import String.
Require Import ExtrHaskellString.
Require Import ROSCOQ.CoList.


(** ROS has a large variety of primitive message types.
   These can be composed into record like constructs.
   A collection of the primitive ROS message types can be found at
   http://wiki.ros.org/std_msgs

   roshask already generates those message types in Haskell
   and handles serialization and deserialization to/from messages. 
   We want to  reuse that effort. 
    This means, for example, that the type for 
    ROS Int8 in Coq should extract to whatever roshask uses for that type,
    which is Data.Int.Int8.
   
   Still, there remains a choice in Coq. We can either axiomatize
   the haskell type Data.Int.Int8 and its operations.
   An alternate approach will be to use a concrete,
   perhaps more logical representation in Coq.
   The extraction directives will be the same, regardless of the choice.
   The latter approach might be convenient for Coq proofs, e.g. one 
   can do proofs by computation.

   For now, we are using the former choice.
 *)


Axiom RoshaskInt8 : Type.
Extract Constant RoshaskInt8 => "Data.Int.Int8".

(*We can add finite field operations, but does Haskels's
   Data.Int.Int8 satisfie the field laws? If so we can assume
   an Instance of MathClasses' Field*)

(* MC Type class instances are  provided below, so one will be able 
   to just use + instead of writing the big names.*)
Axiom  roshaskInt8Add :  RoshaskInt8 -> RoshaskInt8 -> RoshaskInt8.
Extract Constant roshaskInt8Add => "(+)".

Require Export MathClasses.interfaces.canonical_names.
Instance PlusInstanceRoshaskInt8 : Plus RoshaskInt8 := roshaskInt8Add.



