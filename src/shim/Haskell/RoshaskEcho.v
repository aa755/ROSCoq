Require Import RoshaskMsg.
Require Import String.
Require Import ExtrHaskellString.
Require Import RoshaskNodeMonad.
Require Import ROSStringMsg.


Extraction Language Haskell.

Open Scope string_scope.

Require Import MathClasses.interfaces.monads.

Open Scope mc_scope.

Definition chatter : TopicName := "/chatter". (*it's extract is unreadable*)
Definition chatterecho : TopicName := "/chatterecho". (*it's extract is unreadable*)
  
Definition echoNode : Node unit :=
  strmIn  ← (subscribe chatter);
  publish chatterecho strmIn.

Extraction "coqEcho.hs" echoNode.


