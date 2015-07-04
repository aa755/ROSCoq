-----------------------------------------------------------------------------
--
-- Module      :  Rational
-- Copyright   :
-- License     :  ?
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

import Data.Ratio

type HQ = (Ratio Prelude.Integer)

mkQ :: Prelude.Integer -> Prelude.Integer -> HQ
mkQ a b = a % b

qFromFloat :: Prelude.Float -> HQ
qFromFloat a  =  toRational a

qToFloat :: HQ ->  Prelude.Float
qToFloat a  =  fromRational a

hQNum :: HQ -> Prelude.Integer
hQNum x = numerator x

hQDen :: HQ -> Prelude.Integer
hQDen x = denominator x

main = do
    putStrLn ("World")




