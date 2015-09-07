Require Import String.
Require Import ExtrHaskellString.

Definition TopicName : Type := string.

CoInductive TopicStream (T:Type) :=
| TNil : TopicStream T (*should this case be there? I dont see why a topic must deliver infinitely many messages*)
| TCons : T -> TopicStream T -> TopicStream T.

Class RoshashMsgType (T:Type) :=
{
   subscribe : TopicName -> TopicStream T;
   publish : TopicName -> TopicStream T -> unit (*will be mapped to advertize in Roshask*)
}.

(*roshask will be modified to generate Coq Types for ROS message types. These message types
will be instances of the above typeclass. The publish and subscribe implementations will use 
subscribe and advertize methods respectively in roshask.
On top of these functions, the ROSCoq message handler functionality will be built.
*)