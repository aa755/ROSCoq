Require Import String.
Require ExtrHaskellBasic.

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


Require Import CoList.

(** this is not a pure computation. the final result depends on not just
   the values of the 2 streams, but when items in the streams arrived*)
Axiom asapMerge :  forall {A:Type}, CoList A -> CoList A -> Node (CoList A).
Extract Constant asapMerge => "Ros.ROSCoqUtil.asapMergeCoList".

(** lack of productivity is the only thing in the way of this being a pure function.
    We never know if we will keep getting empty lists in input forever. So the
    returned [CoList] cannot be evaluated to either [cnil] or [ccons] in bounded amount 
    of time. Hence we put this computation in the Node monad. 
   Node (CoList A) is an abstract type (neither inductive, nor coinductive).

Not needed anymore?
*)
Axiom flattenCoListList :  forall {A:Type}, CoList (list A)  -> Node (CoList A).
Extract Constant flattenCoListList => "(\ll . return (Prelude.concat ll))".
(** recall that [CoList T] extracts to Haskell as [T]. *)

Axiom coFoldLeft: forall {a b:Type}, (a-> b ->Node a)-> CoList b -> a -> Node a.
Extract Constant coFoldLeft => "Ros.ROSCoqUtil.coFoldLeft".






