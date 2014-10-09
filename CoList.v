
Set Implicit Arguments.

CoInductive CoList (A : Type) : Type :=
    cnil : CoList A | ccons : A -> CoList A -> CoList A.

Fixpoint initialSegment {A} (len : nat) (cl : CoList A) : list A :=
match len with
| 0 => nil
| S len' => match cl with
         | cnil => nil
         | ccons hd tl => cons hd (initialSegment len' tl)
         end
end.


