Require Import String.
Require Import ExtrHaskellString.
Require Import RoshaskNodeMonad.


Definition TopicName : Type := string.

Axiom RTopic : Type -> Type.
(** TODO: generalize over the IO monad. *)

Extract Constant RTopic "a" => "Ros.Node.Topic GHC.Base.IO a".

(* Haskell Definition, which doesn't work in Coq, because m may not be positive
newtype Topic m a = Topic { runTopic :: m (a, Topic m a) } 

CoInductive Topic (m:Type ->Type) `{Monad m} (a:Type) :=
| CTopic (runTopic : m (a × Topic m a)).


Error: Non strictly positive occurrence of "Topic" in
 "m (a × Topic m H H0 H1 H2 a) → Topic m H H0 H1 H2 a". 
*)


(** TODO: make it an instance of functior*)
Axiom tmap : forall {A B :Type}, (A->B) -> RTopic A -> RTopic B.
Extract Constant tmap  => "GHC.Base.fmap".

Axiom tfilter : forall {A B: Type} (f: A -> bool)
                  (g: forall (a:A) {pr: f a = true}, B), RTopic A -> RTopic B.
Extract Constant tfilter  => "\f g l -> GHC.Base.fmap (\x -> g x ()) (Ros.Topic.filter f l)".

(** this is not a pure computation. the final result depends on not just
   the values of the 2 streams, but when items in the streams arrived*)
Axiom asapMerge :  forall {A:Type}, (RTopic A) -> (RTopic A) -> (RTopic A).
Extract Constant asapMerge => "Ros.Topic.Util.merge".

Axiom flattenTL : forall {A:Type}, (RTopic (list A)) -> (RTopic A).
Extract Constant flattenTL => "Ros.ROSCoqUtil.flattenTL".

Axiom foldMapL : forall {s a b :Type}, s -> (s -> a -> (b * s)) -> RTopic a -> RTopic b.
Extract Constant foldMapL => "Ros.ROSCoqUtil.foldMapL".







