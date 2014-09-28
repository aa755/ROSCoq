CoInductive Process (In Out : Type) :=
buildP : In 
          -> ((Process In Out)* Out)
          -> Process In Out.

