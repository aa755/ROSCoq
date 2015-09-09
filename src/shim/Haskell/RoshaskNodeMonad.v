Require Import String.

Extraction Language Haskell.

Axiom Node : Type -> Type.
Extract Constant Node "a" => "Ros.Node.Node a".

(** I doubt that Coq typeclasses
  get extracted to Haskell typeclasses. It makes sense to do the resolution in Coq.
  So, we have extraction directives specifically for the return and bind functions of Node.
*)

Axiom nreturn : forall {a:Type}, a  -> Node a.
Extract Constant nreturn => "Ros.ROSCoqUtil.nreturn".
(* Extract Constant nreturn "a" => "Ros.ROSCoqUtil.nreturn a". *)

Definition example : Node nat := nreturn 0.
Recursive Extraction example.

Axiom nbind : forall {a b:Type},  Node a -> (a -> Node b) -> Node b.
Extract Constant nbind => "Ros.ROSCoqUtil.nbind".

Require Import MathClasses.interfaces.monads.

Instance ReturnInstanceNodeHaskell : MonadReturn Node := (fun A => @nreturn A).
(* TODO : change the order of params in Haskell too *)
Instance BindInstanceNodeHaskell : MonadBind Node := (fun A B f x=> @nbind A B x f).

(* Assuming that, for all (Equiv) instances of equality on Node A, Node A is a monad. 
   Should this assumption be only for eq?
*)
Axiom AssumeMonadNodeHaskell: forall nodeEq, @Monad Node nodeEq _ _.

Instance MonadInstanceNodeHaskell : forall nodeEq, @Monad Node nodeEq _ _ :=
  AssumeMonadNodeHaskell.





