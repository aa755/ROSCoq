
Set Implicit Arguments.

CoInductive CoList (A : Type) : Type :=
    cnil : CoList A | ccons : A -> CoList A -> CoList A.


(*
Extraction to ML.

Recursive Extraction CoList.

type 'a coList = 'a __coList Lazy.t
and 'a __coList =
| Cnil
| Ccons of 'a * 'a coList
*)


Extraction Language Haskell.

(*
Extraction to Haskell

Recursive Extraction CoList.

data CoList a =
   Cnil
 | Ccons a (CoList a)
*)


Extract Inductive CoList => "([])" [ "[]" "
(:)" ].


Extract Inductive list => "([])" [ "[]" "
(:)" ].


Fixpoint initialSegment {A} (len : nat) (cl : CoList A) : list A :=
match len with
| 0 => nil
| S len' => match cl with
         | cnil _ => nil
         | ccons hd tl => cons hd (initialSegment len' tl)
         end
end.


Section Map.
  Variables A B : Type.
  Variable f : A -> B.

CoFixpoint coMap (l:CoList A) : CoList B :=
    match l with
      | cnil _ => cnil B
      | ccons a t => ccons (f a) (coMap t)
    end.

End Map.

