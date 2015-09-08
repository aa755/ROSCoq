module CoList where

import qualified Prelude

data Nat =
   O
 | S Nat

initialSegment :: Nat -> (([]) a1) -> ([]) a1
initialSegment len cl =
  case len of {
   O -> [];
   S len' ->
    case cl of {
     [] -> [];
      (:) hd tl ->  (:) hd (initialSegment len' tl)}}

