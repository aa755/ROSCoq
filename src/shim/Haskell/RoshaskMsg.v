Require Import String.
Require Import ExtrHaskellString.
Require Import ROSCOQ.CoList.


Definition TopicName : Type := string.

(** These are streams that can be published/subscribed to/from ROS topics.
    However, there can be streams which are 
    only used for intermediate results, or even stremas
    which have nothing to do with topics.
    
    One can think of [ROSStream T] as [Topic IO T] in roshask.
    Note that the notation [] in comments has nothing to do with lists.
    These are coqdoc directives to indicate that the thing inside is a code object.
  *)
Definition ROSStream (T:Type) := CoList T.

Class RoshashMsgType (T:Type) :=
  {
    (** Ideally, these functions should be put in a monad which gets extracted
      to the Node monad of roshask. 
     Then one can directly use these functions on Coq programs.
     Currently, these are there just to implement the ROSCoq message handlers.
     *)
    (** Found a suitable definition of Monads in Coq:
https://github.com/coq-ext-lib/coq-ext-lib/blob/4af1a22651e3397435636c1b15d3a27829a3537c/theories/Structures/Monad.v#L8 
  It even has Haskell like notations defined. However I doubt that Coq typeclasses
  get extracted to Haskell typeclasses. It makes sense to do the resolution in Coq.
  So, we would just put extraction directives for the return and bind functions of
  the particular Coq instance,
  to the concrete bind and return functions of the Node monad in roshak
*)
    
   subscribe : TopicName -> ROSStream T;
   publish : TopicName -> ROSStream T -> unit (*will be mapped to advertize in Roshask*)
}.

(**roshask will be modified to generate Coq Types for ROS message types. These message types
will be instances of the above typeclass. The publish and subscribe implementations will use 
subscribe and advertize methods respectively in roshask.
On top of these functions, the ROSCoq message handler functionality will be built.
*)
