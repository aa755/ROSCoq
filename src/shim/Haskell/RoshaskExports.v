Require Import String.
Require Import RoshaskMsg.

Extraction Language Haskell.

Axiom Node : Type -> Type.
Extract Constant Node "'a" => "Ros.Node 'a".

Axiom nreturn : forall a:Type, a  -> Node a.

nbind:: Node a -> (a -> Node b) -> Node b
nbind x f =  x >>= f

-- | When Coq types are generated for ROS message, this function will be specialized to that message type.
-- TopicName is just String. If this changes in upstream, the Coq API and this function will have to be updated.
subscribeCoList::(RosBinary a, MsgInfo a, Typeable a) => TopicName -> Node [a]
subscribeCoList s =
    do
       t <- (subscribe s)
       toListN t

-- | When Coq types are generated for ROS message, this function will be specialized to that message type.
-- TopicName is just String. If this changes in upstream, the Coq API and this function will have to be updated.
publishCoList::(RosBinary a, MsgInfo a, Typeable a) => TopicName -> [a] -> Node ()
publishCoList s l = advertise s (fromList l)


