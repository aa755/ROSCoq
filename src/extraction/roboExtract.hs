{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module RoboExtract where

import qualified Prelude
import Data.Ratio

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif


#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif


#ifdef __GLASGOW_HASKELL__
type Any = GHC.Prim.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x0 f y0 =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x0 f y0 =
  eq_rect x0 f y0

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x0 h y0 =
  eq_rec x0 h y0

data Nat =
   O
 | S Nat

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x0 y0 -> x0}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) x0 y0 -> y0}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
compSpec2Type x0 y0 c =
  compareSpec2Type c

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

nat_iter :: Nat -> (a1 -> a1) -> a1 -> a1
nat_iter n f x0 =
  case n of {
   O -> x0;
   S n' -> f (nat_iter n' f x0)}

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Prelude.Bool -> Reflect
iff_reflect b =
  case b of {
   Prelude.True -> and_rec (\_ _ -> ReflectT);
   Prelude.False -> and_rec (\_ _ -> ReflectF)}

compose :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
compose g f x0 =
  g (f x0)

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

positive_rect :: (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1 ->
                 a1) -> a1 -> Prelude.Integer -> a1
positive_rect f f0 f1 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    f p0 (positive_rect f f0 f1 p0))
    (\p0 ->
    f0 p0 (positive_rect f f0 f1 p0))
    (\_ ->
    f1)
    p

positive_rec :: (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1 ->
                a1) -> a1 -> Prelude.Integer -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Prelude.Integer

n_rect :: a1 -> (Prelude.Integer -> a1) -> N -> a1
n_rect f f0 n =
  case n of {
   N0 -> f;
   Npos x0 -> f0 x0}

n_rec :: a1 -> (Prelude.Integer -> a1) -> N -> a1
n_rec =
  n_rect

z_rect :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
          Prelude.Integer -> a1
z_rect f f0 f1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    f)
    (\x0 ->
    f0 x0)
    (\x0 ->
    f1 x0)
    z

z_rec :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
         Prelude.Integer -> a1
z_rec =
  z_rect

type T = Prelude.Integer

succ :: Prelude.Integer -> Prelude.Integer
succ x0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x)
    (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    p)
    (\_ -> (\x -> 2 Prelude.* x)
    1)
    x0

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x)
      (succ p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      p)
      y0)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      q)
      (\_ -> (\x -> 2 Prelude.* x)
      1)
      y0)
    x0

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (succ p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x)
      (succ p))
      y0)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (succ q))
      (\q -> (\x -> 2 Prelude.* x)
      (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      1)
      y0)
    x0

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    (pred_double p))
    (\_ ->
    1)
    x0

pred :: Prelude.Integer -> Prelude.Integer
pred x0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x)
    p)
    (\p ->
    pred_double p)
    (\_ ->
    1)
    x0

pred_N :: Prelude.Integer -> N
pred_N x0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> Npos ((\x -> 2 Prelude.* x)
    p))
    (\p -> Npos
    (pred_double p))
    (\_ ->
    N0)
    x0

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

mask_rect :: a1 -> (Prelude.Integer -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos x0 -> f0 x0;
   IsNeg -> f1}

mask_rec :: a1 -> (Prelude.Integer -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x0 =
  case x0 of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos ((\x -> 2 Prelude.* x Prelude.+ 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x0 =
  case x0 of {
   IsPos p -> IsPos ((\x -> 2 Prelude.* x) p);
   x1 -> x1}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> IsPos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    p)))
    (\p -> IsPos ((\x -> 2 Prelude.* x)
    (pred_double p)))
    (\_ ->
    IsNul)
    x0

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 -> IsPos
      (pred q))
      (\p0 -> IsPos
      (pred q))
      (\_ ->
      IsNul)
      q;
   _ -> IsNeg}

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask p q))
      (\q ->
      succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> 2 Prelude.* x)
      p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y0)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p ->
      IsNeg)
      (\p ->
      IsNeg)
      (\_ ->
      IsNul)
      y0)
    x0

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask_carry p q))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\_ ->
      double_pred_mask p)
      y0)
    (\_ ->
    IsNeg)
    x0

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub x0 y0 =
  case sub_mask x0 y0 of {
   IsPos z -> z;
   _ -> 1}

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    add y0 ((\x -> 2 Prelude.* x) (mul p y0)))
    (\p -> (\x -> 2 Prelude.* x)
    (mul p y0))
    (\_ ->
    y0)
    x0

iter :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter n f x0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\n' ->
    f (iter n' f (iter n' f x0)))
    (\n' ->
    iter n' f (iter n' f x0))
    (\_ ->
    f x0)
    n

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow x0 y0 =
  iter y0 (mul x0) 1

square :: Prelude.Integer -> Prelude.Integer
square p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    (add (square p0) p0)))
    (\p0 -> (\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    (square p0)))
    (\_ ->
    1)
    p

div2 :: Prelude.Integer -> Prelude.Integer
div2 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    p0)
    (\p0 ->
    p0)
    (\_ ->
    1)
    p

div2_up :: Prelude.Integer -> Prelude.Integer
div2_up p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    succ p0)
    (\p0 ->
    p0)
    (\_ ->
    1)
    p

size_nat :: Prelude.Integer -> Nat
size_nat p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> S
    (size_nat p0))
    (\p0 -> S
    (size_nat p0))
    (\_ -> S
    O)
    p

size :: Prelude.Integer -> Prelude.Integer
size p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    succ (size p0))
    (\p0 ->
    succ (size p0))
    (\_ ->
    1)
    p

compare_cont :: Prelude.Integer -> Prelude.Integer -> Comparison ->
                Comparison
compare_cont x0 y0 r =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont p q r)
      (\q ->
      compare_cont p q Gt)
      (\_ ->
      Gt)
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont p q Lt)
      (\q ->
      compare_cont p q r)
      (\_ ->
      Gt)
      y0)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      Lt)
      (\q ->
      Lt)
      (\_ ->
      r)
      y0)
    x0

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare x0 y0 =
  compare_cont x0 y0 Eq

min :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
min p p' =
  case compare p p' of {
   Gt -> p';
   _ -> p}

max :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
max p p' =
  case compare p p' of {
   Gt -> p;
   _ -> p'}

eqb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 ->
      eqb p0 q0)
      (\p1 ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p1 ->
      Prelude.False)
      (\q0 ->
      eqb p0 q0)
      (\_ ->
      Prelude.False)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      q)
    p

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb x0 y0 =
  case compare x0 y0 of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb x0 y0 =
  case compare x0 y0 of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

sqrtrem_step :: (Prelude.Integer -> Prelude.Integer) -> (Prelude.Integer ->
                Prelude.Integer) -> ((,) Prelude.Integer Mask) -> (,)
                Prelude.Integer Mask
sqrtrem_step f g p =
  case p of {
   (,) s y0 ->
    case y0 of {
     IsPos r ->
      let {s' = (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) s)}
      in
      let {r' = g (f r)} in
      case leb s' r' of {
       Prelude.True -> (,) ((\x -> 2 Prelude.* x Prelude.+ 1) s)
        (sub_mask r' s');
       Prelude.False -> (,) ((\x -> 2 Prelude.* x) s) (IsPos r')};
     _ -> (,) ((\x -> 2 Prelude.* x) s)
      (sub_mask (g (f 1)) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))}}

sqrtrem :: Prelude.Integer -> (,) Prelude.Integer Mask
sqrtrem p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p1 ->
      sqrtrem_step (\x0 -> (\x -> 2 Prelude.* x Prelude.+ 1) x0) (\x0 ->
        (\x -> 2 Prelude.* x Prelude.+ 1) x0) (sqrtrem p1))
      (\p1 ->
      sqrtrem_step (\x0 -> (\x -> 2 Prelude.* x) x0) (\x0 ->
        (\x -> 2 Prelude.* x Prelude.+ 1) x0) (sqrtrem p1))
      (\_ -> (,) 1 (IsPos ((\x -> 2 Prelude.* x)
      1)))
      p0)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p1 ->
      sqrtrem_step (\x0 -> (\x -> 2 Prelude.* x Prelude.+ 1) x0) (\x0 ->
        (\x -> 2 Prelude.* x) x0) (sqrtrem p1))
      (\p1 ->
      sqrtrem_step (\x0 -> (\x -> 2 Prelude.* x) x0) (\x0 ->
        (\x -> 2 Prelude.* x) x0) (sqrtrem p1))
      (\_ -> (,) 1 (IsPos
      1))
      p0)
    (\_ -> (,) 1
    IsNul)
    p

sqrt :: Prelude.Integer -> Prelude.Integer
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcdn n a b =
  case n of {
   O -> 1;
   S n0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\a' ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\b' ->
        case compare a' b' of {
         Eq -> a;
         Lt -> gcdn n0 (sub b' a') a;
         Gt -> gcdn n0 (sub a' b') b})
        (\b0 ->
        gcdn n0 a b0)
        (\_ ->
        1)
        b)
      (\a0 ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\p ->
        gcdn n0 a0 b)
        (\b0 -> (\x -> 2 Prelude.* x)
        (gcdn n0 a0 b0))
        (\_ ->
        1)
        b)
      (\_ ->
      1)
      a}

gcd :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd a b =
  gcdn (plus (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
         ((,) Prelude.Integer Prelude.Integer)
ggcdn n a b =
  case n of {
   O -> (,) 1 ((,) a b);
   S n0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\a' ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\b' ->
        case compare a' b' of {
         Eq -> (,) a ((,) 1 1);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa (add aa ((\x -> 2 Prelude.* x) ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,) (add bb ((\x -> 2 Prelude.* x) ab)) bb)}}})
        (\b0 ->
        case ggcdn n0 a b0 of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) aa ((\x -> 2 Prelude.* x) bb))}})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\a0 ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\p ->
        case ggcdn n0 a0 b of {
         (,) g p0 ->
          case p0 of {
           (,) aa bb -> (,) g ((,) ((\x -> 2 Prelude.* x) aa) bb)}})
        (\b0 ->
        case ggcdn n0 a0 b0 of {
         (,) g p -> (,) ((\x -> 2 Prelude.* x) g) p})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\_ -> (,) 1 ((,) 1
      b))
      a}

ggcd :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
        ((,) Prelude.Integer Prelude.Integer)
ggcd a b =
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x0 =
  case x0 of {
   N0 -> Npos 1;
   Npos p -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos ((\x -> 2 Prelude.* x) p)}

lor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (lor p0 q0))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (lor p0 q0))
      (\_ ->
      p)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (lor p0 q0))
      (\q0 -> (\x -> 2 Prelude.* x)
      (lor p0 q0))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      p0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      q)
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1)
      q0)
      (\_ ->
      q)
      q)
    p

land :: Prelude.Integer -> Prelude.Integer -> N
land p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 ->
      nsucc_double (land p0 q0))
      (\q0 ->
      ndouble (land p0 q0))
      (\_ -> Npos
      1)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (land p0 q0))
      (\q0 ->
      ndouble (land p0 q0))
      (\_ ->
      N0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 -> Npos
      1)
      (\q0 ->
      N0)
      (\_ -> Npos
      1)
      q)
    p

ldiff :: Prelude.Integer -> Prelude.Integer -> N
ldiff p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\q0 ->
      nsucc_double (ldiff p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x)
      p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\_ -> Npos
      p)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      N0)
      (\q0 -> Npos
      1)
      (\_ ->
      N0)
      q)
    p

lxor :: Prelude.Integer -> Prelude.Integer -> N
lxor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (lxor p0 q0))
      (\q0 ->
      nsucc_double (lxor p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x)
      p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 ->
      nsucc_double (lxor p0 q0))
      (\q0 ->
      ndouble (lxor p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1)
      p0))
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> Npos ((\x -> 2 Prelude.* x)
      q0))
      (\q0 -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1)
      q0))
      (\_ ->
      N0)
      q)
    p

shiftl_nat :: Prelude.Integer -> Nat -> Prelude.Integer
shiftl_nat p n =
  nat_iter n (\x0 -> (\x -> 2 Prelude.* x) x0) p

shiftr_nat :: Prelude.Integer -> Nat -> Prelude.Integer
shiftr_nat p n =
  nat_iter n div2 p

shiftl :: Prelude.Integer -> N -> Prelude.Integer
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 (\x0 -> (\x -> 2 Prelude.* x) x0) p}

shiftr :: Prelude.Integer -> N -> Prelude.Integer
shiftr p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 div2 p}

testbit_nat :: Prelude.Integer -> Nat -> Prelude.Bool
testbit_nat p n =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    case n of {
     O -> Prelude.True;
     S n' -> testbit_nat p0 n'})
    (\p0 ->
    case n of {
     O -> Prelude.False;
     S n' -> testbit_nat p0 n'})
    (\_ ->
    case n of {
     O -> Prelude.True;
     S n0 -> Prelude.False})
    p

testbit :: Prelude.Integer -> N -> Prelude.Bool
testbit p n =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    case n of {
     N0 -> Prelude.True;
     Npos n0 -> testbit p0 (pred_N n0)})
    (\p0 ->
    case n of {
     N0 -> Prelude.False;
     Npos n0 -> testbit p0 (pred_N n0)})
    (\_ ->
    case n of {
     N0 -> Prelude.True;
     Npos p0 -> Prelude.False})
    p

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    op a (iter_op op p0 (op a a)))
    (\p0 ->
    iter_op op p0 (op a a))
    (\_ ->
    a)
    p

to_nat :: Prelude.Integer -> Nat
to_nat x0 =
  iter_op plus x0 (S O)

of_nat :: Nat -> Prelude.Integer
of_nat n =
  case n of {
   O -> 1;
   S x0 ->
    case x0 of {
     O -> 1;
     S n0 -> succ (of_nat x0)}}

of_succ_nat :: Nat -> Prelude.Integer
of_succ_nat n =
  case n of {
   O -> 1;
   S x0 -> succ (of_succ_nat x0)}

eq_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eq_dec x0 y0 =
  positive_rec (\p h y1 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (h p0))
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      y1) (\p h y1 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (h p0))
      (\_ ->
      Prelude.False)
      y1) (\y1 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p ->
      Prelude.False)
      (\p ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      y1) x0 y0

peano_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
peano_rect a f p =
  let {
   f2 = peano_rect (f 1 a) (\p0 x0 ->
          f (succ ((\x -> 2 Prelude.* x) p0))
            (f ((\x -> 2 Prelude.* x) p0) x0))}
  in
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\q ->
    f ((\x -> 2 Prelude.* x) q) (f2 q))
    (\q ->
    f2 q)
    (\_ ->
    a)
    p

peano_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Prelude.Integer PeanoView

peanoView_rect :: a1 -> (Prelude.Integer -> PeanoView -> a1 -> a1) ->
                  Prelude.Integer -> PeanoView -> a1
peanoView_rect f f0 p p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p1 p2 -> f0 p1 p2 (peanoView_rect f f0 p1 p2)}

peanoView_rec :: a1 -> (Prelude.Integer -> PeanoView -> a1 -> a1) ->
                 Prelude.Integer -> PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Prelude.Integer -> PeanoView -> PeanoView
peanoView_xO p q =
  case q of {
   PeanoOne -> PeanoSucc 1 PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc (succ ((\x -> 2 Prelude.* x) p0)) (PeanoSucc
    ((\x -> 2 Prelude.* x) p0) (peanoView_xO p0 q0))}

peanoView_xI :: Prelude.Integer -> PeanoView -> PeanoView
peanoView_xI p q =
  case q of {
   PeanoOne -> PeanoSucc (succ 1) (PeanoSucc 1 PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc (succ ((\x -> 2 Prelude.* x Prelude.+ 1) p0))
    (PeanoSucc ((\x -> 2 Prelude.* x Prelude.+ 1) p0) (peanoView_xI p0 q0))}

peanoView :: Prelude.Integer -> PeanoView
peanoView p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    peanoView_xI p0 (peanoView p0))
    (\p0 ->
    peanoView_xO p0 (peanoView p0))
    (\_ ->
    PeanoOne)
    p

peanoView_iter :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer ->
                  PeanoView -> a1
peanoView_iter a f p q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Prelude.Integer -> Prelude.Integer -> Reflect
eqb_spec x0 y0 =
  iff_reflect (eqb x0 y0)

switch_Eq :: Comparison -> Comparison -> Comparison
switch_Eq c c' =
  case c' of {
   Eq -> c;
   x0 -> x0}

mask2cmp :: Mask -> Comparison
mask2cmp p =
  case p of {
   IsNul -> Eq;
   IsPos p0 -> Gt;
   IsNeg -> Lt}

leb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec0 x0 y0 =
  iff_reflect (leb x0 y0)

ltb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec0 x0 y0 =
  iff_reflect (ltb x0 y0)

max_case_strong :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                   Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (() ->
                   a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max n m) __ (hl __);
   _ -> compat m (max n m) __ (hr __)}

max_case :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
            Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case n m x0 x1 x2 =
  max_case_strong n m x0 (\_ -> x1) (\_ -> x2)

max_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
max_dec n m =
  max_case n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

min_case_strong :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                   Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (() ->
                   a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min n m) __ (hr __);
   _ -> compat n (min n m) __ (hl __)}

min_case :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
            Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case n m x0 x1 x2 =
  min_case_strong n m x0 (\_ -> x1) (\_ -> x2)

min_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
min_dec n m =
  min_case n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

max_case_strong0 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong0 n m x0 x1 =
  max_case_strong n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

max_case0 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
max_case0 n m x0 x1 =
  max_case_strong0 n m (\_ -> x0) (\_ -> x1)

max_dec0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
max_dec0 =
  max_dec

min_case_strong0 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong0 n m x0 x1 =
  min_case_strong n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

min_case0 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
min_case0 n m x0 x1 =
  min_case_strong0 n m (\_ -> x0) (\_ -> x1)

min_dec0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
min_dec0 =
  min_dec

type T0 = N

zero :: N
zero =
  N0

one :: N
one =
  Npos 1

two :: N
two =
  Npos ((\x -> 2 Prelude.* x) 1)

succ_double :: N -> N
succ_double x0 =
  case x0 of {
   N0 -> Npos 1;
   Npos p -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p)}

double :: N -> N
double n =
  case n of {
   N0 -> N0;
   Npos p -> Npos ((\x -> 2 Prelude.* x) p)}

succ0 :: N -> N
succ0 n =
  case n of {
   N0 -> Npos 1;
   Npos p -> Npos (succ p)}

pred0 :: N -> N
pred0 n =
  case n of {
   N0 -> N0;
   Npos p -> pred_N p}

succ_pos :: N -> Prelude.Integer
succ_pos n =
  case n of {
   N0 -> 1;
   Npos p -> succ p}

add0 :: N -> N -> N
add0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (add p q)}}

sub0 :: N -> N -> N
sub0 n m =
  case n of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n;
     Npos m' ->
      case sub_mask n' m' of {
       IsPos p -> Npos p;
       _ -> N0}}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> Npos (mul p q)}}

compare0 :: N -> N -> Comparison
compare0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Eq;
     Npos m' -> Lt};
   Npos n' ->
    case m of {
     N0 -> Gt;
     Npos m' -> compare n' m'}}

eqb0 :: N -> N -> Prelude.Bool
eqb0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Prelude.True;
     Npos p -> Prelude.False};
   Npos p ->
    case m of {
     N0 -> Prelude.False;
     Npos q -> eqb p q}}

leb0 :: N -> N -> Prelude.Bool
leb0 x0 y0 =
  case compare0 x0 y0 of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb0 :: N -> N -> Prelude.Bool
ltb0 x0 y0 =
  case compare0 x0 y0 of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

min0 :: N -> N -> N
min0 n n' =
  case compare0 n n' of {
   Gt -> n';
   _ -> n}

max0 :: N -> N -> N
max0 n n' =
  case compare0 n n' of {
   Gt -> n;
   _ -> n'}

div0 :: N -> N
div0 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p -> Npos
      p)
      (\p -> Npos
      p)
      (\_ ->
      N0)
      p0}

even :: N -> Prelude.Bool
even n =
  case n of {
   N0 -> Prelude.True;
   Npos p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p}

odd :: N -> Prelude.Bool
odd n =
  Prelude.not (even n)

pow0 :: N -> N -> N
pow0 n p =
  case p of {
   N0 -> Npos 1;
   Npos p0 ->
    case n of {
     N0 -> N0;
     Npos q -> Npos (pow q p0)}}

square0 :: N -> N
square0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (square p)}

log2 :: N -> N
log2 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p -> Npos
      (size p))
      (\p -> Npos
      (size p))
      (\_ ->
      N0)
      p0}

size0 :: N -> N
size0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (size p)}

size_nat0 :: N -> Nat
size_nat0 n =
  case n of {
   N0 -> O;
   Npos p -> size_nat p}

pos_div_eucl :: Prelude.Integer -> N -> (,) N N
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}})
    (\_ ->
    case b of {
     N0 -> (,) N0 (Npos 1);
     Npos p ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\p0 -> (,) N0 (Npos
        1))
        (\p0 -> (,) N0 (Npos
        1))
        (\_ -> (,) (Npos 1)
        N0)
        p})
    a

div_eucl :: N -> N -> (,) N N
div_eucl a b =
  case a of {
   N0 -> (,) N0 N0;
   Npos na ->
    case b of {
     N0 -> (,) N0 a;
     Npos p -> pos_div_eucl na b}}

div :: N -> N -> N
div a b =
  fst (div_eucl a b)

modulo :: N -> N -> N
modulo a b =
  snd (div_eucl a b)

gcd0 :: N -> N -> N
gcd0 a b =
  case a of {
   N0 -> b;
   Npos p ->
    case b of {
     N0 -> a;
     Npos q -> Npos (gcd p q)}}

ggcd0 :: N -> N -> (,) N ((,) N N)
ggcd0 a b =
  case a of {
   N0 -> (,) b ((,) N0 (Npos 1));
   Npos p ->
    case b of {
     N0 -> (,) a ((,) (Npos 1) N0);
     Npos q ->
      case ggcd p q of {
       (,) g p0 ->
        case p0 of {
         (,) aa bb -> (,) (Npos g) ((,) (Npos aa) (Npos bb))}}}}

sqrtrem0 :: N -> (,) N N
sqrtrem0 n =
  case n of {
   N0 -> (,) N0 N0;
   Npos p ->
    case sqrtrem p of {
     (,) s m ->
      case m of {
       IsPos r -> (,) (Npos s) (Npos r);
       _ -> (,) (Npos s) N0}}}

sqrt0 :: N -> N
sqrt0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (sqrt p)}

lor0 :: N -> N -> N
lor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> ldiff p q}}

lxor0 :: N -> N -> N
lxor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> lxor p q}}

shiftl_nat0 :: N -> Nat -> N
shiftl_nat0 a n =
  nat_iter n double a

shiftr_nat0 :: N -> Nat -> N
shiftr_nat0 a n =
  nat_iter n div0 a

shiftl0 :: N -> N -> N
shiftl0 a n =
  case a of {
   N0 -> N0;
   Npos a0 -> Npos (shiftl a0 n)}

shiftr0 :: N -> N -> N
shiftr0 a n =
  case n of {
   N0 -> a;
   Npos p -> iter p div0 a}

testbit_nat0 :: N -> Nat -> Prelude.Bool
testbit_nat0 a =
  case a of {
   N0 -> (\x0 -> Prelude.False);
   Npos p -> testbit_nat p}

testbit0 :: N -> N -> Prelude.Bool
testbit0 a n =
  case a of {
   N0 -> Prelude.False;
   Npos p -> testbit p n}

to_nat0 :: N -> Nat
to_nat0 a =
  case a of {
   N0 -> O;
   Npos p -> to_nat p}

of_nat0 :: Nat -> N
of_nat0 n =
  case n of {
   O -> N0;
   S n' -> Npos (of_succ_nat n')}

iter0 :: N -> (a1 -> a1) -> a1 -> a1
iter0 n f x0 =
  case n of {
   N0 -> x0;
   Npos p -> iter p f x0}

eq_dec0 :: N -> N -> Prelude.Bool
eq_dec0 n m =
  n_rec (\m0 ->
    case m0 of {
     N0 -> Prelude.True;
     Npos p -> Prelude.False}) (\p m0 ->
    case m0 of {
     N0 -> Prelude.False;
     Npos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0)}) n m

discr :: N -> Prelude.Maybe Prelude.Integer
discr n =
  case n of {
   N0 -> Prelude.Nothing;
   Npos p -> Prelude.Just p}

binary_rect :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rect f0 f2 fS2 n =
  let {f2' = \p -> f2 (Npos p)} in
  let {fS2' = \p -> fS2 (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> positive_rect fS2' f2' (fS2 N0 f0) p}

binary_rec :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rec =
  binary_rect

peano_rect0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rect0 f0 f n =
  let {f' = \p -> f (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> peano_rect (f N0 f0) f' p}

peano_rec0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rec0 =
  peano_rect0

leb_spec1 :: N -> N -> Reflect
leb_spec1 x0 y0 =
  iff_reflect (leb0 x0 y0)

ltb_spec1 :: N -> N -> Reflect
ltb_spec1 x0 y0 =
  iff_reflect (ltb0 x0 y0)

recursion :: a1 -> (N -> a1 -> a1) -> N -> a1
recursion =
  peano_rect0

sqrt_up :: N -> N
sqrt_up a =
  case compare0 N0 a of {
   Lt -> succ0 (sqrt0 (pred0 a));
   _ -> N0}

log2_up :: N -> N
log2_up a =
  case compare0 (Npos 1) a of {
   Lt -> succ0 (log2 (pred0 a));
   _ -> N0}

lcm :: N -> N -> N
lcm a b =
  mul0 a (div b (gcd0 a b))

eqb_spec0 :: N -> N -> Reflect
eqb_spec0 x0 y0 =
  iff_reflect (eqb0 x0 y0)

b2n :: Prelude.Bool -> N
b2n b =
  case b of {
   Prelude.True -> Npos 1;
   Prelude.False -> N0}

setbit :: N -> N -> N
setbit a n =
  lor0 a (shiftl0 (Npos 1) n)

clearbit :: N -> N -> N
clearbit a n =
  ldiff0 a (shiftl0 (Npos 1) n)

ones :: N -> N
ones n =
  pred0 (shiftl0 (Npos 1) n)

lnot :: N -> N -> N
lnot a n =
  lxor0 a (ones n)

max_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat n (max0 n m) __ (hl __);
   _ -> compat m (max0 n m) __ (hr __)}

max_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case1 n m x0 x1 x2 =
  max_case_strong1 n m x0 (\_ -> x1) (\_ -> x2)

max_dec1 :: N -> N -> Prelude.Bool
max_dec1 n m =
  max_case1 n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

min_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

min_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case1 n m x0 x1 x2 =
  min_case_strong1 n m x0 (\_ -> x1) (\_ -> x2)

min_dec1 :: N -> N -> Prelude.Bool
min_dec1 n m =
  min_case1 n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

max_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
max_case_strong2 n m x0 x1 =
  max_case_strong1 n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

max_case2 :: N -> N -> a1 -> a1 -> a1
max_case2 n m x0 x1 =
  max_case_strong2 n m (\_ -> x0) (\_ -> x1)

max_dec2 :: N -> N -> Prelude.Bool
max_dec2 =
  max_dec1

min_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
min_case_strong2 n m x0 x1 =
  min_case_strong1 n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

min_case2 :: N -> N -> a1 -> a1 -> a1
min_case2 n m x0 x1 =
  min_case_strong2 n m (\_ -> x0) (\_ -> x1)

min_dec2 :: N -> N -> Prelude.Bool
min_dec2 =
  min_dec1

type T1 = Prelude.Integer

zero0 :: Prelude.Integer
zero0 =
  0

one0 :: Prelude.Integer
one0 =
  (\x -> x) 1

two0 :: Prelude.Integer
two0 =
  (\x -> x) ((\x -> 2 Prelude.* x) 1)

double0 :: Prelude.Integer -> Prelude.Integer
double0 x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x)
    p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x)
    p))
    x0

succ_double0 :: Prelude.Integer -> Prelude.Integer
succ_double0 x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x)
    1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    (\p -> Prelude.negate
    (pred_double p))
    x0

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate
    1)
    (\p -> (\x -> x)
    (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    x0

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      double0 (pos_sub p q))
      (\q ->
      succ_double0 (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x)
      p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      pred_double0 (pos_sub p q))
      (\q ->
      double0 (pos_sub p q))
      (\_ -> (\x -> x)
      (pred_double p))
      y0)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x)
      q))
      (\q -> Prelude.negate
      (pred_double q))
      (\_ ->
      0)
      y0)
    x0

opp :: Prelude.Integer -> Prelude.Integer
opp x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\x1 -> Prelude.negate
    x1)
    (\x1 -> (\x -> x)
    x1)
    x0

succ1 :: Prelude.Integer -> Prelude.Integer
succ1 x0 =
  (Prelude.+) x0 ((\x -> x) 1)

pred1 :: Prelude.Integer -> Prelude.Integer
pred1 x0 =
  (Prelude.+) x0 (Prelude.negate 1)

pow_pos :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow_pos z n =
  iter n ((Prelude.*) z) ((\x -> x) 1)

pow1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow1 x0 y0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x)
    1)
    (\p ->
    pow_pos x0 p)
    (\p ->
    0)
    y0

square1 :: Prelude.Integer -> Prelude.Integer
square1 x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    (square p))
    (\p -> (\x -> x)
    (square p))
    x0

compare1 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare1 x0 y0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Eq)
      (\y' ->
      Lt)
      (\y' ->
      Gt)
      y0)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Gt)
      (\y' ->
      compare x' y')
      (\y' ->
      Gt)
      y0)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Lt)
      (\y' ->
      Lt)
      (\y' ->
      compOpp (compare x' y'))
      y0)
    x0

sgn :: Prelude.Integer -> Prelude.Integer
sgn z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    1)
    (\p -> Prelude.negate
    1)
    z

leb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb1 x0 y0 =
  case compare1 x0 y0 of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb1 x0 y0 =
  case compare1 x0 y0 of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

geb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
geb x0 y0 =
  case compare1 x0 y0 of {
   Lt -> Prelude.False;
   _ -> Prelude.True}

gtb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
gtb x0 y0 =
  case compare1 x0 y0 of {
   Gt -> Prelude.True;
   _ -> Prelude.False}

eqb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb1 x0 y0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.True)
      (\p ->
      Prelude.False)
      (\p ->
      Prelude.False)
      y0)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\q ->
      eqb p q)
      (\p0 ->
      Prelude.False)
      y0)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\p0 ->
      Prelude.False)
      (\q ->
      eqb p q)
      y0)
    x0

abs :: Prelude.Integer -> Prelude.Integer
abs z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    p)
    (\p -> (\x -> x)
    p)
    z

abs_nat :: Prelude.Integer -> Nat
abs_nat z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    O)
    (\p ->
    to_nat p)
    (\p ->
    to_nat p)
    z

abs_N :: Prelude.Integer -> N
abs_N z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    N0)
    (\p -> Npos
    p)
    (\p -> Npos
    p)
    z

to_nat1 :: Prelude.Integer -> Nat
to_nat1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    O)
    (\p ->
    to_nat p)
    (\p ->
    O)
    z

to_N :: Prelude.Integer -> N
to_N z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    N0)
    (\p -> Npos
    p)
    (\p ->
    N0)
    z

of_nat1 :: Nat -> Prelude.Integer
of_nat1 n =
  case n of {
   O -> 0;
   S n0 -> (\x -> x) (of_succ_nat n0)}

of_N :: N -> Prelude.Integer
of_N n =
  case n of {
   N0 -> 0;
   Npos p -> (\x -> x) p}

to_pos :: Prelude.Integer -> Prelude.Integer
to_pos z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    1)
    (\p ->
    p)
    (\p ->
    1)
    z

iter1 :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter1 n f x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    x0)
    (\p ->
    iter p f x0)
    (\p ->
    x0)
    n

pos_div_eucl0 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
                 Prelude.Integer
pos_div_eucl0 a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {
       r' = (Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb1 r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r} in
      case ltb1 r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\_ ->
    case leb1 ((\x -> x) ((\x -> 2 Prelude.* x) 1)) b of {
     Prelude.True -> (,) 0 ((\x -> x) 1);
     Prelude.False -> (,) ((\x -> x) 1) 0})
    a

div_eucl0 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
             Prelude.Integer
div_eucl0 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) 0
    0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0
      0)
      (\p ->
      pos_div_eucl0 a' b)
      (\b' ->
      case pos_div_eucl0 a' ((\x -> x) b') of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (opp q)
          0)
          (\p -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          (\p -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0
      0)
      (\p ->
      case pos_div_eucl0 a' b of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (opp q)
          0)
          (\p0 -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          (\p0 -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          r})
      (\b' ->
      case pos_div_eucl0 a' ((\x -> x) b') of {
       (,) q r -> (,) q (opp r)})
      b)
    a

div1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div1 = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

modulo0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo0 = (\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)

quotrem :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
           Prelude.Integer
quotrem a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) 0
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0
      a)
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (of_N q) (of_N r)})
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (opp (of_N q)) (of_N r)})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0
      a)
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (opp (of_N q)) (opp (of_N r))})
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (of_N q) (opp (of_N r))})
      b)
    a

quot :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
quot a b =
  fst (quotrem a b)

rem :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
rem a b =
  snd (quotrem a b)

even0 :: Prelude.Integer -> Prelude.Bool
even0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    Prelude.True)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p)
    z

odd0 :: Prelude.Integer -> Prelude.Bool
odd0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    Prelude.False)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.True)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 ->
      Prelude.True)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      p)
    z

div3 :: Prelude.Integer -> Prelude.Integer
div3 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 -> (\x -> x)
      (div2 p))
      (\p0 -> (\x -> x)
      (div2 p))
      (\_ ->
      0)
      p)
    (\p -> Prelude.negate
    (div2_up p))
    z

quot2 :: Prelude.Integer -> Prelude.Integer
quot2 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 -> (\x -> x)
      (div2 p))
      (\p0 -> (\x -> x)
      (div2 p))
      (\_ ->
      0)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 -> Prelude.negate
      (div2 p))
      (\p0 -> Prelude.negate
      (div2 p))
      (\_ ->
      0)
      p)
    z

log0 :: Prelude.Integer -> Prelude.Integer
log0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p -> (\x -> x)
      (size p))
      (\p -> (\x -> x)
      (size p))
      (\_ ->
      0)
      p0)
    (\p ->
    0)
    z

sqrtrem1 :: Prelude.Integer -> (,) Prelude.Integer Prelude.Integer
sqrtrem1 n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) 0
    0)
    (\p ->
    case sqrtrem p of {
     (,) s m ->
      case m of {
       IsPos r -> (,) ((\x -> x) s) ((\x -> x) r);
       _ -> (,) ((\x -> x) s) 0}})
    (\p -> (,) 0
    0)
    n

sqrt1 :: Prelude.Integer -> Prelude.Integer
sqrt1 n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    (sqrt p))
    (\p ->
    0)
    n

gcd1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    abs b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      abs a)
      (\b0 -> (\x -> x)
      (gcd a0 b0))
      (\b0 -> (\x -> x)
      (gcd a0 b0))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      abs a)
      (\b0 -> (\x -> x)
      (gcd a0 b0))
      (\b0 -> (\x -> x)
      (gcd a0 b0))
      b)
    a

ggcd1 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
         ((,) Prelude.Integer Prelude.Integer)
ggcd1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) (abs b) ((,) 0
    (sgn b)))
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) (abs a) ((,) (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((\x -> x) g) ((,) ((\x -> x) aa) ((\x -> x) bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((\x -> x) g) ((,) ((\x -> x) aa) (Prelude.negate
          bb))}})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) (abs a) ((,) (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((\x -> x) g) ((,) (Prelude.negate aa) ((\x -> x)
          bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((\x -> x) g) ((,) (Prelude.negate aa)
          (Prelude.negate bb))}})
      b)
    a

testbit1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
testbit1 a n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    odd0 a)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\a0 ->
      testbit a0 (Npos p))
      (\a0 ->
      Prelude.not (testbit0 (pred_N a0) (Npos p)))
      a)
    (\p ->
    Prelude.False)
    n

shiftl1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftl1 a n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    a)
    (\p ->
    iter p ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1))) a)
    (\p ->
    iter p div3 a)
    n

shiftr1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftr1 a n =
  shiftl1 a (opp n)

lor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> (\x -> x)
      (lor a0 b0))
      (\b0 -> Prelude.negate
      (succ_pos (ldiff0 (pred_N b0) (Npos a0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (ldiff0 (pred_N a0) (Npos b0))))
      (\b0 -> Prelude.negate
      (succ_pos (land0 (pred_N a0) (pred_N b0))))
      b)
    a

land1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
land1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      0)
      (\b0 ->
      of_N (land a0 b0))
      (\b0 ->
      of_N (ldiff0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      0)
      (\b0 ->
      of_N (ldiff0 (Npos b0) (pred_N a0)))
      (\b0 -> Prelude.negate
      (succ_pos (lor0 (pred_N a0) (pred_N b0))))
      b)
    a

ldiff1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ldiff1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 ->
      of_N (ldiff a0 b0))
      (\b0 ->
      of_N (land0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (lor0 (pred_N a0) (Npos b0))))
      (\b0 ->
      of_N (ldiff0 (pred_N b0) (pred_N a0)))
      b)
    a

lxor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lxor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 ->
      of_N (lxor a0 b0))
      (\b0 -> Prelude.negate
      (succ_pos (lxor0 (Npos a0) (pred_N b0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (lxor0 (pred_N a0) (Npos b0))))
      (\b0 ->
      of_N (lxor0 (pred_N a0) (pred_N b0)))
      b)
    a

eq_dec1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eq_dec1 x0 y0 =
  z_rec (\y1 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.True)
      (\p ->
      Prelude.False)
      (\p ->
      Prelude.False)
      y1) (\p y1 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0))
      (\p0 ->
      Prelude.False)
      y1) (\p y1 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\p0 ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0))
      y1) x0 y0

leb_spec2 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec2 x0 y0 =
  iff_reflect (leb1 x0 y0)

ltb_spec2 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec2 x0 y0 =
  iff_reflect (ltb1 x0 y0)

sqrt_up0 :: Prelude.Integer -> Prelude.Integer
sqrt_up0 a =
  case compare1 0 a of {
   Lt -> succ1 (sqrt1 (pred1 a));
   _ -> 0}

log2_up0 :: Prelude.Integer -> Prelude.Integer
log2_up0 a =
  case compare1 ((\x -> x) 1) a of {
   Lt -> succ1 (log0 (pred1 a));
   _ -> 0}

div4 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div4 =
  quot

modulo1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo1 =
  rem

lcm0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lcm0 a b =
  abs ((Prelude.*) a (div1 b (gcd1 a b)))

eqb_spec1 :: Prelude.Integer -> Prelude.Integer -> Reflect
eqb_spec1 x0 y0 =
  iff_reflect (eqb1 x0 y0)

b2z :: Prelude.Bool -> Prelude.Integer
b2z b =
  case b of {
   Prelude.True -> (\x -> x) 1;
   Prelude.False -> 0}

setbit0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
setbit0 a n =
  lor1 a (shiftl1 ((\x -> x) 1) n)

clearbit0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
clearbit0 a n =
  ldiff1 a (shiftl1 ((\x -> x) 1) n)

lnot0 :: Prelude.Integer -> Prelude.Integer
lnot0 a =
  pred1 (opp a)

ones0 :: Prelude.Integer -> Prelude.Integer
ones0 n =
  pred1 (shiftl1 ((\x -> x) 1) n)

max_case_strong3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                    Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat n (Prelude.max n m) __ (hl __);
   _ -> compat m (Prelude.max n m) __ (hr __)}

max_case3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
             Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case3 n m x0 x1 x2 =
  max_case_strong3 n m x0 (\_ -> x1) (\_ -> x2)

max_dec3 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
max_dec3 n m =
  max_case3 n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

min_case_strong3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                    Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat m (Prelude.min n m) __ (hr __);
   _ -> compat n (Prelude.min n m) __ (hl __)}

min_case3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
             Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case3 n m x0 x1 x2 =
  min_case_strong3 n m x0 (\_ -> x1) (\_ -> x2)

min_dec3 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
min_dec3 n m =
  min_case3 n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

max_case_strong4 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong4 n m x0 x1 =
  max_case_strong3 n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

max_case4 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
max_case4 n m x0 x1 =
  max_case_strong4 n m (\_ -> x0) (\_ -> x1)

max_dec4 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
max_dec4 =
  max_dec3

min_case_strong4 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong4 n m x0 x1 =
  min_case_strong3 n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

min_case4 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
min_case4 n m x0 x1 =
  min_case_strong4 n m (\_ -> x0) (\_ -> x1)

min_dec4 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
min_dec4 =
  min_dec3

z_lt_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_dec x0 y0 =
  case compare1 x0 y0 of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

z_lt_ge_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_ge_dec x0 y0 =
  z_lt_dec x0 y0

z_lt_le_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_le_dec x0 y0 =
  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (z_lt_ge_dec x0 y0)

pow_pos0 :: (a1 -> a1 -> a1) -> a1 -> Prelude.Integer -> a1
pow_pos0 rmul x0 i =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\i0 ->
    let {p = pow_pos0 rmul x0 i0} in rmul x0 (rmul p p))
    (\i0 ->
    let {p = pow_pos0 rmul x0 i0} in rmul p p)
    (\_ ->
    x0)
    i

type DecEq t =
  t -> t -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_DecEq
  
eqdec :: (DecEq a1) -> a1 -> a1 -> Prelude.Bool
eqdec decEq =
  decEq

type Csymmetric a r = a -> a -> r -> r

data Stream a =
   Cons a (Stream a)

hd :: (Stream a1) -> a1
hd x0 =
  case x0 of {
   Cons a s -> a}

tl :: (Stream a1) -> Stream a1
tl x0 =
  case x0 of {
   Cons a s -> s}

map0 :: (a1 -> a2) -> (Stream a1) -> Stream a2
map0 f s =
  Cons (f (hd s)) (map0 f (tl s))

zipWith :: (a1 -> a2 -> a3) -> (Stream a1) -> (Stream a2) -> Stream a3
zipWith f a b =
  Cons (f (hd a) (hd b)) (zipWith f (tl a) (tl b))

type Cast a b = a -> b

cast :: (Cast a1 a2) -> a1 -> a2
cast cast0 =
  cast0

type Plus a = a -> a -> a

plus0 :: (Plus a1) -> a1 -> a1 -> a1
plus0 plus1 =
  plus1

type Mult a = a -> a -> a

mult :: (Mult a1) -> a1 -> a1 -> a1
mult mult0 =
  mult0

type One a = a

one1 :: (One a1) -> a1
one1 one2 =
  one2

type Zero a = a

zero1 :: (Zero a1) -> a1
zero1 zero2 =
  zero2

type Negate a = a -> a

negate :: (Negate a1) -> a1 -> a1
negate negate0 =
  negate0

type NonNeg r = r

type Decision = Prelude.Bool

decide :: Decision -> Prelude.Bool
decide decision =
  decision

decide_rel :: (a1 -> a2 -> Decision) -> a1 -> a2 -> Decision
decide_rel dec x0 y0 =
  dec x0 y0

data RSetoid =
   Build_RSetoid

type St_car = Any

type Cotransitive a r = a -> a -> r -> a -> Prelude.Either r r

data Is_CSetoid a ap =
   Build_is_CSetoid (Csymmetric a ap) (Cotransitive a ap)

data CSetoid =
   MakeCSetoid RSetoid (Is_CSetoid St_car Any)

cs_crr :: CSetoid -> RSetoid
cs_crr c =
  case c of {
   MakeCSetoid cs_crr0 cs_proof -> cs_crr0}

type Cs_ap = Any

build_CSetoid :: (Is_CSetoid a1 a2) -> CSetoid
build_CSetoid p =
  MakeCSetoid Build_RSetoid (unsafeCoerce p)

type Bin_fun_strext =
  St_car -> St_car -> St_car -> St_car -> Cs_ap -> Prelude.Either Cs_ap Cs_ap

data CSetoid_bin_fun =
   Build_CSetoid_bin_fun (St_car -> St_car -> St_car) Bin_fun_strext

csbf_fun :: CSetoid -> CSetoid -> CSetoid -> CSetoid_bin_fun -> St_car ->
            St_car -> St_car
csbf_fun s1 s2 s3 c =
  case c of {
   Build_CSetoid_bin_fun csbf_fun0 csbf_strext -> csbf_fun0}

type CSetoid_bin_op = CSetoid_bin_fun

data CSemiGroup =
   Build_CSemiGroup CSetoid CSetoid_bin_op

csg_crr :: CSemiGroup -> CSetoid
csg_crr c =
  case c of {
   Build_CSemiGroup csg_crr0 csg_op0 -> csg_crr0}

csg_op :: CSemiGroup -> CSetoid_bin_op
csg_op c =
  case c of {
   Build_CSemiGroup csg_crr0 csg_op0 -> csg_op0}

type SqrtFun a b = a -> b

sqrtFun :: (SqrtFun a1 a2) -> a1 -> a2
sqrtFun sqrtFun0 =
  sqrtFun0

type RealNumberPi r = r

__U03c0_ :: (RealNumberPi a1) -> a1
__U03c0_ realNumberPi =
  realNumberPi

type HalfNum r = r

half_num :: (HalfNum a1) -> a1
half_num halfNum =
  halfNum

type NormSpace a b = a -> b

norm :: (NormSpace a1 a2) -> a1 -> a2
norm normSpace =
  normSpace

data Cart2D t =
   MkCart2D t t

x :: (Cart2D a1) -> a1
x c =
  case c of {
   MkCart2D x0 y0 -> x0}

y :: (Cart2D a1) -> a1
y c =
  case c of {
   MkCart2D x0 y0 -> y0}

data Polar2D t =
   MkPolar2D t t

rad :: (Polar2D a1) -> a1
rad p =
  case p of {
   MkPolar2D rad0 __U03b8_0 -> rad0}

__U03b8_ :: (Polar2D a1) -> a1
__U03b8_ p =
  case p of {
   MkPolar2D rad0 __U03b8_0 -> __U03b8_0}

normSpace_instance_Cart2D :: (SqrtFun a1 a2) -> (Plus a1) -> (Mult a1) ->
                             NormSpace (Cart2D a1) a2
normSpace_instance_Cart2D h h0 h1 cart =
  sqrtFun h
    (plus0 h0 (mult h1 (x cart) (x cart)) (mult h1 (y cart) (y cart)))

qnum :: (Ratio Prelude.Integer) -> Prelude.Integer
qnum q =
  (\fp qn -> fp (numerator qn) (denominator qn))
    (\qnum0 qden0 ->
    qnum0)
    q

qden :: (Ratio Prelude.Integer) -> Prelude.Integer
qden q =
  (\fp qn -> fp (numerator qn) (denominator qn))
    (\qnum0 qden0 ->
    qden0)
    q

inject_Z :: Prelude.Integer -> (Ratio Prelude.Integer)
inject_Z x0 =
  (\x y -> x % y) x0 1

qcompare :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) -> Comparison
qcompare p q =
  compare1 ((Prelude.*) (qnum p) ((\x -> x) (qden q)))
    ((Prelude.*) (qnum q) ((\x -> x) (qden p)))

qeq_dec :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) -> Prelude.Bool
qeq_dec x0 y0 =
  eq_dec1 ((Prelude.*) (qnum x0) ((\x -> x) (qden y0)))
    ((Prelude.*) (qnum y0) ((\x -> x) (qden x0)))

qplus :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
         (Ratio Prelude.Integer)
qplus x0 y0 =
  (\x y -> x % y)
    ((Prelude.+) ((Prelude.*) (qnum x0) ((\x -> x) (qden y0)))
      ((Prelude.*) (qnum y0) ((\x -> x) (qden x0))))
    (mul (qden x0) (qden y0))

qmult :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
         (Ratio Prelude.Integer)
qmult x0 y0 =
  (\x y -> x % y) ((Prelude.*) (qnum x0) (qnum y0)) (mul (qden x0) (qden y0))

qopp :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer)
qopp x0 =
  (\x y -> x % y) (opp (qnum x0)) (qden x0)

qminus :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
          (Ratio Prelude.Integer)
qminus x0 y0 =
  qplus x0 (qopp y0)

qinv :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer)
qinv x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x y -> x % y) 0
    1)
    (\p -> (\x y -> x % y) ((\x -> x) (qden x0))
    p)
    (\p -> (\x y -> x % y) (Prelude.negate (qden x0))
    p)
    (qnum x0)

qdiv :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
        (Ratio Prelude.Integer)
qdiv x0 y0 =
  qmult x0 (qinv y0)

qlt_le_dec :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
              Prelude.Bool
qlt_le_dec x0 y0 =
  z_lt_le_dec ((Prelude.*) (qnum x0) ((\x -> x) (qden y0)))
    ((Prelude.*) (qnum y0) ((\x -> x) (qden x0)))

qpower_positive :: (Ratio Prelude.Integer) -> Prelude.Integer ->
                   (Ratio Prelude.Integer)
qpower_positive q p =
  pow_pos0 qmult q p

qpower :: (Ratio Prelude.Integer) -> Prelude.Integer ->
          (Ratio Prelude.Integer)
qpower q z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x y -> x % y) ((\x -> x) 1)
    1)
    (\p ->
    qpower_positive q p)
    (\p ->
    qinv (qpower_positive q p))
    z

qred :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer)
qred q =
  (\fp qn -> fp (numerator qn) (denominator qn))
    (\q1 q2 ->
    case snd (ggcd1 q1 ((\x -> x) q2)) of {
     (,) r1 r2 -> (\x y -> x % y) r1 (to_pos r2)})
    q

qminus' :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
           (Ratio Prelude.Integer)
qminus' x0 y0 =
  qred (qminus x0 y0)

qabs :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer)
qabs x0 =
  (\fp qn -> fp (numerator qn) (denominator qn))
    (\n d -> (\x y -> x % y) (abs n)
    d)
    x0

qfloor :: (Ratio Prelude.Integer) -> Prelude.Integer
qfloor x0 =
  (\fp qn -> fp (numerator qn) (denominator qn))
    (\n d ->
    div1 n ((\x -> x) d))
    x0

ap_Q_cotransitive0 :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
                      (Ratio Prelude.Integer) -> Prelude.Either () ()
ap_Q_cotransitive0 x0 y0 z =
  case qeq_dec x0 z of {
   Prelude.True -> Prelude.Right __;
   Prelude.False -> Prelude.Left __}

qplus_strext0 :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
                 (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
                 Prelude.Either Any Any
qplus_strext0 x1 x2 y1 y2 =
  case qeq_dec x1 x2 of {
   Prelude.True -> Prelude.Right __;
   Prelude.False -> Prelude.Left __}

ap_Q_cotransitive1 :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
                      (Ratio Prelude.Integer) -> Prelude.Either () ()
ap_Q_cotransitive1 x0 y0 z =
  ap_Q_cotransitive0 x0 y0 z

ap_Q_is_apartness :: Is_CSetoid (Ratio Prelude.Integer) ()
ap_Q_is_apartness =
  Build_is_CSetoid __ (\x0 x1 _ -> ap_Q_cotransitive1 x0 x1)

q_as_CSetoid :: CSetoid
q_as_CSetoid =
  build_CSetoid ap_Q_is_apartness

q_is_Setoid :: RSetoid
q_is_Setoid =
  cs_crr q_as_CSetoid

qplus_strext1 :: St_car -> St_car -> St_car -> St_car -> Prelude.Either 
                 Cs_ap Cs_ap
qplus_strext1 x1 x2 y1 y2 =
  qplus_strext0 (unsafeCoerce x1) (unsafeCoerce x2) (unsafeCoerce y1)
    (unsafeCoerce y2)

qplus_is_bin_fun :: CSetoid_bin_fun
qplus_is_bin_fun =
  Build_CSetoid_bin_fun (unsafeCoerce qplus) (\x0 x1 x2 x3 _ ->
    qplus_strext1 x0 x1 x2 x3)

q_as_CSemiGroup :: CSemiGroup
q_as_CSemiGroup =
  Build_CSemiGroup q_as_CSetoid qplus_is_bin_fun

type MsgHandlerType s i o = s -> i -> (,) s o

data Process in0 out =
   Build_Process Any (MsgHandlerType Any in0 out)

type Qpos = (Ratio Prelude.Integer)

qposMake :: Prelude.Integer -> Prelude.Integer -> Qpos
qposMake num den =
  (\x y -> x % y) ((\x -> x) num) den

qposAsQ :: Qpos -> (Ratio Prelude.Integer)
qposAsQ =
  proj1_sig

mkQpos :: (Ratio Prelude.Integer) -> Qpos
mkQpos a =
  a

qpos_one :: Qpos
qpos_one =
  (\x y -> x % y) ((\x -> x) 1) 1

qpos_mult :: Qpos -> Qpos -> Qpos
qpos_mult x0 y0 =
  qmult (qposAsQ x0) (qposAsQ y0)

qpos_inv :: Qpos -> Qpos
qpos_inv x0 =
  qinv (qposAsQ x0)

qabsQpos :: (Ratio Prelude.Integer) -> Qpos
qabsQpos x0 =
  (\fp qn -> fp (numerator qn) (denominator qn))
    (\qnum0 ad ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      qpos_one)
      (\an ->
      qposMake an ad)
      (\an ->
      qposMake an ad)
      qnum0)
    x0

data RosTopicType rT =
   Build_RosTopicType

type TopicType rT = Any

type Header =
  (Ratio Prelude.Integer)
  -- singleton inductive, whose constructor was mkHeader
  
type Message rosTopic = (,) (SigT rosTopic (TopicType rosTopic)) Header

transport :: a1 -> a1 -> a2 -> a2
transport a b pa =
  eq_rect a pa b

getPayloadR :: (DecEq a1) -> (RosTopicType a1) -> a1 -> (SigT a1
               (TopicType a1)) -> Prelude.Maybe (TopicType a1)
getPayloadR deq h topic m =
  case m of {
   ExistT tp pl ->
    case eqdec deq tp topic of {
     Prelude.True -> Prelude.Just (transport tp topic pl);
     Prelude.False -> Prelude.Nothing}}

getPayload :: (DecEq a1) -> (RosTopicType a1) -> a1 -> (Message a1) ->
              Prelude.Maybe (TopicType a1)
getPayload deq h topic m =
  getPayloadR deq h topic (fst m)

mkDelayedMesg :: (DecEq a1) -> (RosTopicType a1) -> a1 ->
                 (Ratio Prelude.Integer) -> (TopicType a1) -> Message 
                 a1
mkDelayedMesg deq h outTopic delay payload =
  (,) (ExistT outTopic payload) delay

type PureProcWDelay rosTopic =
  (TopicType rosTopic) -> ([])
  ((,) (Ratio Prelude.Integer) (TopicType rosTopic))

delayedLift2Mesg :: (DecEq a1) -> (RosTopicType a1) -> a1 -> a1 ->
                    (PureProcWDelay a1) -> (Message a1) -> ([]) (Message a1)
delayedLift2Mesg deq h inTopic outTopic f inpMesg =
  case getPayload deq h inTopic inpMesg of {
   Prelude.Just tmesg ->
    map (\p -> mkDelayedMesg deq h outTopic (fst p) (snd p)) (f tmesg);
   Prelude.Nothing -> ([])}

min1 :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> a1
min1 le_total x0 y0 =
  case le_total x0 y0 of {
   Prelude.True -> x0;
   Prelude.False -> y0}

min_case5 :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> (() -> a2) -> (() ->
             a2) -> a2
min_case5 le_total x0 y0 hx hy =
  case le_total x0 y0 of {
   Prelude.True -> hx __;
   Prelude.False -> hy __}

max1 :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> a1
max1 le_total x0 y0 =
  case le_total y0 x0 of {
   Prelude.True -> x0;
   Prelude.False -> y0}

max_case5 :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> (() -> a2) -> (() ->
             a2) -> a2
max_case5 le_total x0 y0 x1 x2 =
  let {flip_le_total = \x3 y1 -> le_total y1 x3} in
  min_case5 flip_le_total x0 y0 x1 x2

qlt_le_dec_fast :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
                   Prelude.Bool
qlt_le_dec_fast x0 y0 =
  let {c = qcompare x0 y0} in
  case c of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

qle_total :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
             Prelude.Bool
qle_total x0 y0 =
  qlt_le_dec_fast x0 y0

qmin :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
        (Ratio Prelude.Integer)
qmin =
  min1 qle_total

qmax :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
        (Ratio Prelude.Integer)
qmax =
  max1 qle_total

data QposInf =
   Qpos2QposInf Qpos
 | QposInfinity

qposInf_bind :: (Qpos -> QposInf) -> QposInf -> QposInf
qposInf_bind f x0 =
  case x0 of {
   Qpos2QposInf x' -> f x';
   QposInfinity -> QposInfinity}

qposInf_mult :: QposInf -> QposInf -> QposInf
qposInf_mult x0 y0 =
  qposInf_bind (\x' ->
    qposInf_bind (\y' -> Qpos2QposInf (qpos_mult x' y')) y0) x0

type MetricSpace =
  RSetoid
  -- singleton inductive, whose constructor was Build_MetricSpace
  
ball_ex_dec :: MetricSpace -> (Qpos -> St_car -> St_car -> Prelude.Bool) ->
               QposInf -> St_car -> St_car -> Prelude.Bool
ball_ex_dec x0 ball_dec e a b =
  case e of {
   Qpos2QposInf e0 -> ball_dec e0 a b;
   QposInfinity -> Prelude.True}

data UniformlyContinuousFunction =
   Build_UniformlyContinuousFunction (St_car -> St_car) (Qpos -> QposInf)

ucFun :: MetricSpace -> MetricSpace -> UniformlyContinuousFunction -> St_car
         -> St_car
ucFun x0 y0 u =
  case u of {
   Build_UniformlyContinuousFunction ucFun0 mu0 -> ucFun0}

mu :: MetricSpace -> MetricSpace -> UniformlyContinuousFunction -> Qpos ->
      QposInf
mu x0 y0 u =
  case u of {
   Build_UniformlyContinuousFunction ucFun0 mu0 -> mu0}

uc_Setoid :: MetricSpace -> MetricSpace -> RSetoid
uc_Setoid x0 y0 =
  Build_RSetoid

uniformlyContinuousSpace :: MetricSpace -> MetricSpace -> MetricSpace
uniformlyContinuousSpace x0 y0 =
  uc_Setoid x0 y0

ucFun2 :: MetricSpace -> MetricSpace -> MetricSpace -> St_car -> St_car ->
          St_car -> St_car
ucFun2 x0 y0 z f x1 y1 =
  ucFun y0 z
    (unsafeCoerce
      (ucFun x0 (uniformlyContinuousSpace y0 z) (unsafeCoerce f) x1)) y1

uc_compose :: MetricSpace -> MetricSpace -> MetricSpace -> St_car -> St_car
              -> St_car
uc_compose x0 y0 z g f =
  unsafeCoerce (Build_UniformlyContinuousFunction (\x1 ->
    ucFun y0 z (unsafeCoerce g) (ucFun x0 y0 (unsafeCoerce f) x1)) (\e ->
    qposInf_bind (mu x0 y0 (unsafeCoerce f)) (mu y0 z (unsafeCoerce g) e)))

type DecidableMetric = Qpos -> St_car -> St_car -> Prelude.Bool

type RegularFunction =
  QposInf -> St_car
  -- singleton inductive, whose constructor was Build_RegularFunction
  
approximate :: MetricSpace -> RegularFunction -> QposInf -> St_car
approximate x0 r =
  r

regFun_Setoid :: MetricSpace -> RSetoid
regFun_Setoid x0 =
  Build_RSetoid

complete :: MetricSpace -> MetricSpace
complete x0 =
  regFun_Setoid x0

cunit_fun :: MetricSpace -> St_car -> St_car
cunit_fun x0 x1 =
  unsafeCoerce (\x2 -> x1)

cunit :: MetricSpace -> St_car
cunit x0 =
  unsafeCoerce (Build_UniformlyContinuousFunction (cunit_fun x0) (\x1 ->
    Qpos2QposInf x1))

cmap_fun :: MetricSpace -> MetricSpace -> St_car -> St_car -> St_car
cmap_fun x0 y0 f x1 =
  unsafeCoerce (\e ->
    ucFun x0 y0 (unsafeCoerce f)
      (approximate x0 (unsafeCoerce x1)
        (qposInf_bind (mu x0 y0 (unsafeCoerce f)) e)))

cmap :: MetricSpace -> MetricSpace -> St_car -> St_car
cmap x0 y0 f =
  unsafeCoerce (Build_UniformlyContinuousFunction (cmap_fun x0 y0 f)
    (mu x0 y0 (unsafeCoerce f)))

cap_raw :: MetricSpace -> MetricSpace -> St_car -> St_car -> QposInf ->
           St_car
cap_raw x0 y0 f x1 e =
  approximate y0
    (unsafeCoerce
      (ucFun (complete x0) (complete y0)
        (unsafeCoerce
          (cmap x0 y0
            (approximate (uniformlyContinuousSpace x0 y0) (unsafeCoerce f)
              (qposInf_mult (Qpos2QposInf
                (qposMake 1 ((\x -> 2 Prelude.* x) 1))) e)))) x1))
    (qposInf_mult (Qpos2QposInf (qposMake 1 ((\x -> 2 Prelude.* x) 1))) e)

cap_fun :: MetricSpace -> MetricSpace -> St_car -> St_car -> St_car
cap_fun x0 y0 f x1 =
  unsafeCoerce (cap_raw x0 y0 f x1)

cap_modulus :: MetricSpace -> MetricSpace -> St_car -> Qpos -> QposInf
cap_modulus x0 y0 f e =
  mu x0 y0
    (unsafeCoerce
      (approximate (uniformlyContinuousSpace x0 y0) (unsafeCoerce f)
        (Qpos2QposInf
        (qpos_mult (qposMake 1 ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) e))))
    (qpos_mult (qposMake 1 ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) e)

cap_weak :: MetricSpace -> MetricSpace -> St_car -> St_car
cap_weak x0 y0 f =
  unsafeCoerce (Build_UniformlyContinuousFunction (cap_fun x0 y0 f)
    (cap_modulus x0 y0 f))

cap :: MetricSpace -> MetricSpace -> St_car
cap x0 y0 =
  unsafeCoerce (Build_UniformlyContinuousFunction (cap_weak x0 y0) (\x1 ->
    Qpos2QposInf x1))

cmap2 :: MetricSpace -> MetricSpace -> MetricSpace -> St_car -> St_car
cmap2 x0 y0 z f =
  uc_compose (complete x0) (complete (uniformlyContinuousSpace y0 z))
    (uniformlyContinuousSpace (complete y0) (complete z)) (cap y0 z)
    (cmap x0 (uniformlyContinuousSpace y0 z) f)

q_as_MetricSpace :: MetricSpace
q_as_MetricSpace =
  q_is_Setoid

qmetric_dec :: DecidableMetric
qmetric_dec e a b =
  let {c = qopp (qposAsQ e)} in
  let {d = qminus (unsafeCoerce a) (unsafeCoerce b)} in
  let {s = qlt_le_dec_fast d c} in
  case s of {
   Prelude.True -> Prelude.False;
   Prelude.False ->
    let {s0 = qlt_le_dec_fast (qposAsQ e) d} in
    case s0 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

qball_ex_bool :: QposInf -> St_car -> St_car -> Prelude.Bool
qball_ex_bool e a b =
  case ball_ex_dec q_as_MetricSpace qmetric_dec e a b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

lt_dec :: (a1 -> a1 -> Decision) -> a1 -> a1 -> Decision
lt_dec h0 x0 y0 =
  let {filtered_var = decide_rel h0 y0 x0} in
  case filtered_var of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

nonNeg_inject :: (Zero a1) -> Cast (NonNeg a1) a1
nonNeg_inject h3 =
  proj1_sig

q_0 :: Zero (Ratio Prelude.Integer)
q_0 =
  (\x y -> x % y) 0 1

q_1 :: One (Ratio Prelude.Integer)
q_1 =
  (\x y -> x % y) ((\x -> x) 1) 1

q_opp :: Negate (Ratio Prelude.Integer)
q_opp =
  qopp

q_plus :: Plus (Ratio Prelude.Integer)
q_plus =
  qplus

q_mult :: Mult (Ratio Prelude.Integer)
q_mult =
  qmult

decision_instance_0 :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
                       Decision
decision_instance_0 =
  qeq_dec

inject_Z_Q :: Cast Prelude.Integer (Ratio Prelude.Integer)
inject_Z_Q =
  inject_Z

decision_instance_1 :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
                       Decision
decision_instance_1 y0 x0 =
  let {filtered_var = qlt_le_dec x0 y0} in
  case filtered_var of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

cR :: MetricSpace
cR =
  complete q_as_MetricSpace

inject_Q_CR :: Cast (Ratio Prelude.Integer) St_car
inject_Q_CR =
  unsafeCoerce
    (ucFun q_as_MetricSpace (complete q_as_MetricSpace)
      (unsafeCoerce (cunit q_as_MetricSpace)))

qtranslate_uc :: St_car -> St_car
qtranslate_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    csbf_fun (csg_crr q_as_CSemiGroup) (csg_crr q_as_CSemiGroup)
      (csg_crr q_as_CSemiGroup) (csg_op q_as_CSemiGroup) a b) (\x0 ->
    Qpos2QposInf x0))

qplus_uc :: St_car
qplus_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction qtranslate_uc (\x0 ->
    Qpos2QposInf x0))

cRplus_uc :: St_car
cRplus_uc =
  cmap2 q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace qplus_uc

cRplus :: Plus St_car
cRplus =
  ucFun2 cR cR cR cRplus_uc

qopp_uc :: St_car
qopp_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction (unsafeCoerce qopp) (\x0 ->
    Qpos2QposInf x0))

cRopp :: Negate St_car
cRopp =
  ucFun (complete q_as_MetricSpace) (complete q_as_MetricSpace)
    (unsafeCoerce (cmap q_as_MetricSpace q_as_MetricSpace qopp_uc))

qboundBelow_uc :: St_car -> St_car
qboundBelow_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce (qmax (unsafeCoerce a) (unsafeCoerce b))) (\x0 ->
    Qpos2QposInf x0))

qboundAbove_uc :: St_car -> St_car
qboundAbove_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce (qmin (unsafeCoerce a) (unsafeCoerce b))) (\x0 ->
    Qpos2QposInf x0))

qscale_modulus :: (Ratio Prelude.Integer) -> Qpos -> QposInf
qscale_modulus a e =
  (\fp qn -> fp (numerator qn) (denominator qn))
    (\qnum0 ad ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      QposInfinity)
      (\an -> Qpos2QposInf
      (qpos_mult (qposMake ad an) e))
      (\an -> Qpos2QposInf
      (qpos_mult (qposMake ad an) e))
      qnum0)
    a

qscale_uc :: St_car -> St_car
qscale_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce (qmult (unsafeCoerce a) (unsafeCoerce b)))
    (qscale_modulus (unsafeCoerce a)))

scale :: (Ratio Prelude.Integer) -> St_car
scale a =
  cmap q_as_MetricSpace q_as_MetricSpace (qscale_uc (unsafeCoerce a))

qboundAbs :: Qpos -> St_car
qboundAbs c =
  uc_compose q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace
    (qboundBelow_uc (unsafeCoerce (qopp (qposAsQ c))))
    (qboundAbove_uc (unsafeCoerce (qposAsQ c)))

qmult_modulus :: Qpos -> Qpos -> QposInf
qmult_modulus c e =
  Qpos2QposInf (qpos_mult e (qpos_inv c))

qmult_uc :: Qpos -> St_car
qmult_uc c =
  unsafeCoerce (Build_UniformlyContinuousFunction (\a ->
    uc_compose q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace
      (qscale_uc a) (qboundAbs c)) (qmult_modulus c))

cRmult_bounded :: Qpos -> St_car
cRmult_bounded c =
  cmap2 q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace (qmult_uc c)

cR_b :: Qpos -> St_car -> Qpos
cR_b e x0 =
  mkQpos
    (qplus
      (qabs
        (unsafeCoerce
          (approximate q_as_MetricSpace (unsafeCoerce x0) (Qpos2QposInf e))))
      (qposAsQ e))

cRmult :: Mult St_car
cRmult x0 y0 =
  ucFun2 cR cR cR (cRmult_bounded (cR_b (qposMake 1 1) y0)) x0 y0

approximateQ :: (Ratio Prelude.Integer) -> Prelude.Integer ->
                (Ratio Prelude.Integer)
approximateQ x0 p =
  (\fp qn -> fp (numerator qn) (denominator qn))
    (\n d -> (\x y -> x % y)
    (div1 ((Prelude.*) n ((\x -> x) p)) ((\x -> x) d))
    p)
    x0

root_step :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer) ->
             (Ratio Prelude.Integer)
root_step a b =
  qplus (qdiv b ((\x y -> x % y) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) 1))
    (qdiv a
      (qmult ((\x y -> x % y) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) 1) b))

initial_root :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer)
initial_root a =
  qmult ((\x y -> x % y) ((\x -> x) 1) ((\x -> 2 Prelude.* x) 1))
    (qplus a ((\x y -> x % y) ((\x -> x) 1) 1))

root_loop :: (Ratio Prelude.Integer) -> Qpos -> Nat ->
             (Ratio Prelude.Integer) -> Prelude.Integer ->
             (Ratio Prelude.Integer)
root_loop a e n b err =
  case n of {
   O -> b;
   S n' ->
    case qlt_le_dec_fast (qposAsQ e) ((\x y -> x % y) ((\x -> x) 1) err) of {
     Prelude.True ->
      let {err' = mul err err} in
      root_loop a e n'
        (approximateQ (root_step a b) (mul ((\x -> 2 Prelude.* x) 1) err'))
        err';
     Prelude.False -> b}}

sqrt_raw :: (Ratio Prelude.Integer) -> QposInf -> (Ratio Prelude.Integer)
sqrt_raw a e =
  case e of {
   Qpos2QposInf e' ->
    root_loop a e' (S (size_nat (qden (qposAsQ e')))) (initial_root a)
      ((\x -> 2 Prelude.* x) 1);
   QposInfinity -> (\x y -> x % y) ((\x -> x) 1) 1}

rational_sqrt_mid :: (Ratio Prelude.Integer) -> St_car
rational_sqrt_mid a =
  unsafeCoerce (unsafeCoerce (sqrt_raw a))

rational_sqrt_big_bounded :: Nat -> (Ratio Prelude.Integer) -> St_car
rational_sqrt_big_bounded n a =
  case n of {
   O -> inject_Q_CR ((\x y -> x % y) ((\x -> x) 1) 1);
   S n0 ->
    let {
     s = qle_total a ((\x y -> x % y) ((\x -> x) ((\x -> 2 Prelude.* x)
           ((\x -> 2 Prelude.* x) 1))) 1)}
    in
    case s of {
     Prelude.True -> rational_sqrt_mid a;
     Prelude.False ->
      ucFun cR cR
        (unsafeCoerce
          (scale ((\x y -> x % y) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) 1)))
        (rational_sqrt_big_bounded n0
          (qdiv a ((\x y -> x % y) ((\x -> x) ((\x -> 2 Prelude.* x)
            ((\x -> 2 Prelude.* x) 1))) 1)))}}

rational_sqrt_small_bounded :: Nat -> (Ratio Prelude.Integer) -> St_car
rational_sqrt_small_bounded n a =
  case n of {
   O -> rational_sqrt_mid a;
   S n0 ->
    let {s = qle_total a ((\x y -> x % y) ((\x -> x) 1) 1)} in
    case s of {
     Prelude.True ->
      ucFun cR cR
        (unsafeCoerce
          (scale ((\x y -> x % y) ((\x -> x) 1) ((\x -> 2 Prelude.* x) 1))))
        (rational_sqrt_small_bounded n0
          (qmult ((\x y -> x % y) ((\x -> x) ((\x -> 2 Prelude.* x)
            ((\x -> 2 Prelude.* x) 1))) 1) a));
     Prelude.False -> rational_sqrt_mid a}}

rational_sqrt_pos :: (Ratio Prelude.Integer) -> St_car
rational_sqrt_pos a =
  let {s = qle_total ((\x y -> x % y) ((\x -> x) 1) 1) a} in
  case s of {
   Prelude.True ->
    rational_sqrt_big_bounded
      ((\fp qn -> fp (numerator qn) (denominator qn))
         (\n x0 ->
         (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
           (\_ ->
           O)
           (\p ->
           size_nat p)
           (\p ->
           O)
           n)
         a) a;
   Prelude.False ->
    rational_sqrt_small_bounded
      ((\fp qn -> fp (numerator qn) (denominator qn))
         (\x0 d ->
         size_nat d)
         a) a}

rational_sqrt :: (Ratio Prelude.Integer) -> St_car
rational_sqrt a =
  case qlt_le_dec_fast ((\x y -> x % y) 0 1) a of {
   Prelude.True -> rational_sqrt_pos a;
   Prelude.False -> inject_Q_CR ((\x y -> x % y) 0 1)}

iterate :: (a1 -> a1) -> a1 -> Stream a1
iterate f x0 =
  Cons x0 (iterate f (f x0))

takeUntil :: ((Stream a1) -> Prelude.Bool) -> (Stream a1) -> (a1 -> a2 -> a2)
             -> a2 -> a2
takeUntil p s cons nil =
  case p s of {
   Prelude.True -> nil;
   Prelude.False -> cons (hd s) (takeUntil p (tl s) cons nil)}

everyOther :: (Stream a1) -> Stream a1
everyOther s =
  Cons (hd s) (everyOther (tl (tl s)))

mult_Streams :: (Mult a1) -> (Stream a1) -> (Stream a1) -> Stream a1
mult_Streams h1 =
  zipWith (mult h1)

powers_help :: (Mult a1) -> a1 -> a1 -> Stream a1
powers_help h1 a =
  iterate (\y0 -> mult h1 y0 a)

partialAlternatingSumUntil :: ((Stream (Ratio Prelude.Integer)) ->
                              Prelude.Bool) -> (Stream
                              (Ratio Prelude.Integer)) ->
                              (Ratio Prelude.Integer)
partialAlternatingSumUntil p s =
  takeUntil p s qminus' (zero1 q_0)

infiniteAlternatingSum_raw :: (Stream (Ratio Prelude.Integer)) -> QposInf ->
                              (Ratio Prelude.Integer)
infiniteAlternatingSum_raw s __U03b5_ =
  partialAlternatingSumUntil (\s0 ->
    qball_ex_bool __U03b5_ (hd (unsafeCoerce s0))
      (unsafeCoerce ((\x y -> x % y) 0 1))) s

infiniteAlternatingSum :: (Stream (Ratio Prelude.Integer)) -> St_car
infiniteAlternatingSum seq =
  unsafeCoerce (unsafeCoerce (infiniteAlternatingSum_raw seq))

ppositives_help :: Prelude.Integer -> Stream Prelude.Integer
ppositives_help n =
  Cons n (ppositives_help (succ n))

ppositives :: Stream Prelude.Integer
ppositives =
  ppositives_help 1

qrecip_positives :: Stream (Ratio Prelude.Integer)
qrecip_positives =
  map0 (\x0 -> (\x y -> x % y) ((\x -> x) 1) x0) ppositives

arctanSequence :: (Ratio Prelude.Integer) -> Stream (Ratio Prelude.Integer)
arctanSequence a =
  mult_Streams q_mult (everyOther qrecip_positives)
    (powers_help q_mult (qpower a ((\x -> x) ((\x -> 2 Prelude.* x) 1))) a)

rational_arctan_small_pos :: (Ratio Prelude.Integer) -> St_car
rational_arctan_small_pos a =
  infiniteAlternatingSum (arctanSequence a)

rational_arctan_small :: (Ratio Prelude.Integer) -> St_car
rational_arctan_small a =
  let {s = qle_total a ((\x y -> x % y) 0 1)} in
  case s of {
   Prelude.True -> cRopp (rational_arctan_small_pos (qopp a));
   Prelude.False -> rational_arctan_small_pos a}

r_pi :: (Ratio Prelude.Integer) -> St_car
r_pi r =
  ucFun2 cR cR cR cRplus_uc
    (ucFun2 cR cR cR cRplus_uc
      (ucFun cR cR
        (unsafeCoerce
          (scale
            (qmult
              (inject_Z ((\x -> x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
                ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
                1))))))))) r)))
        (rational_arctan_small_pos ((\x y -> x % y) ((\x -> x) 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))
      (ucFun cR cR
        (unsafeCoerce
          (scale
            (qmult
              (inject_Z ((\x -> x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
                ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) r)))
        (rational_arctan_small_pos ((\x y -> x % y) ((\x -> x) 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))
    (ucFun2 cR cR cR cRplus_uc
      (ucFun cR cR
        (unsafeCoerce
          (scale
            (qmult
              (qopp
                (inject_Z ((\x -> x) ((\x -> 2 Prelude.* x)
                  ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                  ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
                  1)))))))) r)))
        (rational_arctan_small_pos ((\x y -> x % y) ((\x -> x) 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x) 1))))))))))))
      (ucFun cR cR
        (unsafeCoerce
          (scale
            (qmult
              (inject_Z ((\x -> x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) r)))
        (rational_arctan_small_pos ((\x y -> x % y) ((\x -> x) 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          1)))))))))))))))))

cRpi :: St_car
cRpi =
  r_pi ((\x y -> x % y) ((\x -> x) 1) 1)

rational_arctan_big_pos :: (Ratio Prelude.Integer) -> St_car
rational_arctan_big_pos a =
  ucFun2 cR cR cR cRplus_uc
    (r_pi ((\x y -> x % y) ((\x -> x) 1) ((\x -> 2 Prelude.* x) 1)))
    (cRopp (rational_arctan_small_pos (qinv a)))

rational_arctan_mid_pos :: (Ratio Prelude.Integer) -> St_car
rational_arctan_mid_pos a =
  ucFun2 cR cR cR cRplus_uc
    (r_pi ((\x y -> x % y) ((\x -> x) 1) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))))
    (rational_arctan_small
      (qdiv (qminus a ((\x y -> x % y) ((\x -> x) 1) 1))
        (qplus a ((\x y -> x % y) ((\x -> x) 1) 1))))

rational_arctan_pos :: (Ratio Prelude.Integer) -> St_car
rational_arctan_pos a =
  let {
   s = qle_total ((\x y -> x % y) ((\x -> x) ((\x -> 2 Prelude.* x) 1))
         ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))) a}
  in
  case s of {
   Prelude.True ->
    let {
     s0 = qle_total ((\x y -> x % y) ((\x -> x)
            ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1)))
            ((\x -> 2 Prelude.* x) 1)) a}
    in
    case s0 of {
     Prelude.True -> rational_arctan_big_pos a;
     Prelude.False -> rational_arctan_mid_pos a};
   Prelude.False -> rational_arctan_small_pos a}

rational_arctan :: (Ratio Prelude.Integer) -> St_car
rational_arctan a =
  let {s = qle_total a ((\x y -> x % y) 0 1)} in
  case s of {
   Prelude.True -> cRopp (rational_arctan_pos (qopp a));
   Prelude.False -> rational_arctan_pos a}

qabs_uc :: St_car
qabs_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction (unsafeCoerce qabs) (\x0 ->
    Qpos2QposInf x0))

cRabs :: St_car
cRabs =
  cmap q_as_MetricSpace q_as_MetricSpace qabs_uc

rational_sqrt_SqrtFun_instance :: SqrtFun (Ratio Prelude.Integer) St_car
rational_sqrt_SqrtFun_instance =
  rational_sqrt

normSpace_instance_0 :: NormSpace St_car St_car
normSpace_instance_0 =
  ucFun cR cR (unsafeCoerce cRabs)

cRpi_RealNumberPi_instance :: RealNumberPi St_car
cRpi_RealNumberPi_instance =
  cRpi

q_Half_instance :: HalfNum (Ratio Prelude.Integer)
q_Half_instance =
  (\x y -> x % y) ((\x -> x) 1) ((\x -> 2 Prelude.* x) 1)

qSign :: (Negate a1) -> (Ratio Prelude.Integer) -> a1 -> a1
qSign h q a =
  case decide (lt_dec decision_instance_1 q (zero1 q_0)) of {
   Prelude.True -> negate h a;
   Prelude.False -> a}

q2Zapprox :: (Ratio Prelude.Integer) -> Prelude.Integer
q2Zapprox q =
  let {qf = qfloor q} in
  case decide
         (decision_instance_1 (qminus q (inject_Z qf)) ((\x y -> x % y)
           ((\x -> x) 1) ((\x -> 2 Prelude.* x) 1))) of {
   Prelude.True -> qf;
   Prelude.False -> (Prelude.+) qf ((\x -> x) 1)}

r2ZApprox :: St_car -> Qpos -> Prelude.Integer
r2ZApprox r eps =
  q2Zapprox
    (unsafeCoerce
      (approximate q_as_MetricSpace (unsafeCoerce r) (Qpos2QposInf eps)))

cast_instance_0 :: Cast Prelude.Integer St_car
cast_instance_0 =
  compose (compose (cast inject_Q_CR) (cast inject_Z_Q)) (\x0 -> (\x -> x)
    x0)

simpleApproximate :: St_car -> Prelude.Integer -> Qpos ->
                     (Ratio Prelude.Integer)
simpleApproximate r den eps =
  (\x y -> x % y) (r2ZApprox (mult cRmult r (cast cast_instance_0 den)) eps)
    den

qSignHalf :: (Ratio Prelude.Integer) -> (Ratio Prelude.Integer)
qSignHalf q =
  qSign q_opp q (half_num q_Half_instance)

polarTheta :: (Cart2D (Ratio Prelude.Integer)) -> St_car
polarTheta cart =
  case decide (decision_instance_0 (x cart) (zero1 q_0)) of {
   Prelude.True -> mult cRmult cRpi (cast inject_Q_CR (qSignHalf (y cart)));
   Prelude.False ->
    let {angle = rational_arctan (qdiv (y cart) (x cart))} in
    case decide (lt_dec decision_instance_1 (x cart) (zero1 q_0)) of {
     Prelude.True ->
      plus0 cRplus angle
        (qSign cRopp (y cart) (__U03c0_ cRpi_RealNumberPi_instance));
     Prelude.False -> angle}}

polar__U03b8_Sign :: (Cart2D (Ratio Prelude.Integer)) ->
                     (Ratio Prelude.Integer)
polar__U03b8_Sign target =
  qSign q_opp (y target) (one1 q_1)

cart2Polar :: (Cart2D (Ratio Prelude.Integer)) -> Polar2D St_car
cart2Polar cart =
  MkPolar2D
    (norm
      (normSpace_instance_Cart2D rational_sqrt_SqrtFun_instance q_plus
        q_mult) cart) (polarTheta cart)

robotPureProgam :: Qpos -> Qpos -> Qpos -> Qpos -> Prelude.Integer -> (Cart2D
                   (Ratio Prelude.Integer)) -> ([])
                   ((,) (Ratio Prelude.Integer)
                   (Polar2D (Ratio Prelude.Integer)))
robotPureProgam rotspeed speed delay delEps delRes target =
  let {polarTarget = cart2Polar target} in
  let {
   rotDuration = mult cRmult
                   (norm normSpace_instance_0 (__U03b8_ polarTarget))
                   (cast inject_Q_CR (qinv (qposAsQ rotspeed)))}
  in
  let {
   translDuration = mult cRmult (rad polarTarget)
                      (cast inject_Q_CR (qinv (qposAsQ speed)))}
  in
  (:) ((,) (zero1 q_0) (MkPolar2D (zero1 q_0)
  (mult q_mult (polar__U03b8_Sign target) (qposAsQ rotspeed)))) ((:) ((,)
  (simpleApproximate rotDuration delRes delEps) (MkPolar2D (zero1 q_0)
  (zero1 q_0))) ((:) ((,) (cast (nonNeg_inject ((\x y -> x % y) 0 1)) delay)
  (MkPolar2D (cast (nonNeg_inject ((\x y -> x % y) 0 1)) speed) (zero1 q_0)))
  ((:) ((,) (simpleApproximate translDuration delRes delEps) (MkPolar2D
  (zero1 q_0) (zero1 q_0))) ([]))))

data Topic =
   VELOCITY
 | TARGETPOS

topic_beq :: Topic -> Topic -> Prelude.Bool
topic_beq x0 y0 =
  case x0 of {
   VELOCITY ->
    case y0 of {
     VELOCITY -> Prelude.True;
     TARGETPOS -> Prelude.False};
   TARGETPOS ->
    case y0 of {
     VELOCITY -> Prelude.False;
     TARGETPOS -> Prelude.True}}

topic_eq_dec :: Topic -> Topic -> Prelude.Bool
topic_eq_dec x0 y0 =
  let {b = topic_beq x0 y0} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

ldskflskdalfkTopic_eq_dec :: DecEq Topic
ldskflskdalfkTopic_eq_dec =
  topic_eq_dec

ttttt :: RosTopicType Topic
ttttt =
  Build_RosTopicType

rotSpeedRadPerSec :: Qpos
rotSpeedRadPerSec =
  qposMake 1 ((\x -> 2 Prelude.* x) 1)

speedMetresPerSec :: Qpos
speedMetresPerSec =
  qposMake 1 ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x) 1)))

delResSecInv :: Prelude.Integer
delResSecInv =
  (\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
    1))))))))

delEpsSec :: Qpos
delEpsSec =
  qposMake 1 ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1)))))))))))))

initDelayLin :: Qpos
initDelayLin =
  qposMake 1 1

robotProgramInstance :: Qpos -> PureProcWDelay Topic
robotProgramInstance delayLinSec =
  unsafeCoerce
    (robotPureProgam rotSpeedRadPerSec speedMetresPerSec delayLinSec
      delEpsSec delResSecInv)

swProcessInstance :: Process (Message Topic) (([]) (Message Topic))
swProcessInstance =
  Build_Process (unsafeCoerce (qposAsQ initDelayLin)) (\ins inm -> (,)
    (unsafeCoerce
      (qmult (unsafeCoerce ins) (plus0 q_plus (one1 q_1) (one1 q_1))))
    (delayedLift2Mesg ldskflskdalfkTopic_eq_dec ttttt TARGETPOS VELOCITY
      (robotProgramInstance (qabsQpos (unsafeCoerce ins))) inm))

target1Metres :: Cart2D (Ratio Prelude.Integer)
target1Metres =
  MkCart2D ((\x y -> x % y) ((\x -> x) 1) 1) ((\x y -> x % y) ((\x -> x) 1)
    1)

robotOutput :: ([])
               ((,) (Ratio Prelude.Integer)
               (Polar2D (Ratio Prelude.Integer)))
robotOutput =
  unsafeCoerce
    (robotProgramInstance initDelayLin (unsafeCoerce target1Metres))

polar2Pair :: ((,) (Ratio Prelude.Integer) (Polar2D (Ratio Prelude.Integer)))
              -> (,) (Ratio Prelude.Integer)
              ((,) (Ratio Prelude.Integer) (Ratio Prelude.Integer))
polar2Pair inp =
  case inp of {
   (,) del pos -> (,) del ((,) (rad pos) (__U03b8_ pos))}

robotOutputShowable :: ([])
                       ((,) (Ratio Prelude.Integer)
                       ((,) (Ratio Prelude.Integer) (Ratio Prelude.Integer)))
robotOutputShowable =
  map polar2Pair robotOutput

projNums :: ((,) (Ratio Prelude.Integer) (Polar2D (Ratio Prelude.Integer)))
            -> (,) ((,) Prelude.Integer Prelude.Integer) Prelude.Integer
projNums inp =
  case inp of {
   (,) del pos -> (,) ((,) (qnum del) (qnum (rad pos))) (qnum (__U03b8_ pos))}

robotOutputInts :: ([])
                   ((,) ((,) Prelude.Integer Prelude.Integer)
                   Prelude.Integer)
robotOutputInts =
  map projNums robotOutput

map3 :: (a1 -> a2) -> ((,) ((,) a1 a1) a1) -> (,) ((,) a2 a2) a2
map3 f inp =
  case inp of {
   (,) xy z ->
    case xy of {
     (,) x0 y0 -> (,) ((,) (f x0) (f y0)) (f z)}}

