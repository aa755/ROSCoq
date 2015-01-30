{- Warning: The extraction is currently set to bypass opacity,
the following opaque constant bodies have been accessed :
 Qsec.ap_Q_cotransitive0 Qsetoid.ap_Q_cotransitive1. -}

{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import qualified Prelude
import qualified GHC.Base


unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

data Bool =
   True
 | False

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x y -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair x y -> y}

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
compSpec2Type x y c =
  compareSpec2Type c

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
proj1_sig :: a1 -> a1
proj1_sig e =
  e

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Sumor a =
   Inleft a
 | Inright

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

nat_iter :: Nat -> (a1 -> a1) -> a1 -> a1
nat_iter n f x =
  case n of {
   O -> x;
   S n' -> f (nat_iter n' f x)}

data Positive =
   XI Positive
 | XO Positive
 | XH

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p0 -> f p0 (positive_rect f f0 f1 p0);
   XO p0 -> f0 p0 (positive_rect f f0 f1 p0);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Positive

n_rect :: a1 -> (Positive -> a1) -> N -> a1
n_rect f f0 n =
  case n of {
   N0 -> f;
   Npos x -> f0 x}

n_rec :: a1 -> (Positive -> a1) -> N -> a1
n_rec =
  n_rect

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

z_rect :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rect f f0 f1 z =
  case z of {
   Z0 -> f;
   Zpos x -> f0 x;
   Zneg x -> f1 x}

z_rec :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rec =
  z_rect

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Bool -> Reflect
iff_reflect b =
  case b of {
   True -> and_rec (\_ _ -> ReflectT);
   False -> and_rec (\_ _ -> ReflectF)}

type T = Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH ->
    case y of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH ->
    case y of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

pred :: Positive -> Positive
pred x =
  case x of {
   XI p -> XO p;
   XO p -> pred_double p;
   XH -> XH}

pred_N :: Positive -> N
pred_N x =
  case x of {
   XI p -> Npos (XO p);
   XO p -> Npos (pred_double p);
   XH -> N0}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

mask_rect :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos x -> f0 x;
   IsNeg -> f1}

mask_rec :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q ->
    case q of {
     XH -> IsNul;
     _ -> IsPos (pred q)};
   _ -> IsNeg}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH ->
    case y of {
     XH -> IsNul;
     _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter :: Positive -> (a1 -> a1) -> a1 -> a1
iter n f x =
  case n of {
   XI n' -> f (iter n' f (iter n' f x));
   XO n' -> iter n' f (iter n' f x);
   XH -> f x}

pow :: Positive -> Positive -> Positive
pow x y =
  iter y (mul x) XH

square :: Positive -> Positive
square p =
  case p of {
   XI p0 -> XI (XO (add (square p0) p0));
   XO p0 -> XO (XO (square p0));
   XH -> XH}

div2 :: Positive -> Positive
div2 p =
  case p of {
   XI p0 -> p0;
   XO p0 -> p0;
   XH -> XH}

div2_up :: Positive -> Positive
div2_up p =
  case p of {
   XI p0 -> succ p0;
   XO p0 -> p0;
   XH -> XH}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

size :: Positive -> Positive
size p =
  case p of {
   XI p0 -> succ (size p0);
   XO p0 -> succ (size p0);
   XH -> XH}

compare_cont :: Positive -> Positive -> Comparison -> Comparison
compare_cont x y r =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont p q r;
     XO q -> compare_cont p q Gt;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont p q Lt;
     XO q -> compare_cont p q r;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare x y =
  compare_cont x y Eq

min :: Positive -> Positive -> Positive
min p p' =
  case compare p p' of {
   Gt -> p';
   _ -> p}

max :: Positive -> Positive -> Positive
max p p' =
  case compare p p' of {
   Gt -> p;
   _ -> p'}

eqb :: Positive -> Positive -> Bool
eqb p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> eqb p0 q0;
     _ -> False};
   XO p0 ->
    case q of {
     XO q0 -> eqb p0 q0;
     _ -> False};
   XH ->
    case q of {
     XH -> True;
     _ -> False}}

leb :: Positive -> Positive -> Bool
leb x y =
  case compare x y of {
   Gt -> False;
   _ -> True}

ltb :: Positive -> Positive -> Bool
ltb x y =
  case compare x y of {
   Lt -> True;
   _ -> False}

sqrtrem_step :: (Positive -> Positive) -> (Positive -> Positive) -> (Prod
                Positive Mask) -> Prod Positive Mask
sqrtrem_step f g p =
  case p of {
   Pair s y ->
    case y of {
     IsPos r ->
      let {s' = XI (XO s)} in
      let {r' = g (f r)} in
      case leb s' r' of {
       True -> Pair (XI s) (sub_mask r' s');
       False -> Pair (XO s) (IsPos r')};
     _ -> Pair (XO s) (sub_mask (g (f XH)) (XO (XO XH)))}}

sqrtrem :: Positive -> Prod Positive Mask
sqrtrem p =
  case p of {
   XI p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XI x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XI x) (sqrtrem p1);
     XH -> Pair XH (IsPos (XO XH))};
   XO p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XO x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XO x) (sqrtrem p1);
     XH -> Pair XH (IsPos XH)};
   XH -> Pair XH IsNul}

sqrt :: Positive -> Positive
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Positive -> Positive -> Positive
gcdn n a b =
  case n of {
   O -> XH;
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> a;
         Lt -> gcdn n0 (sub b' a') a;
         Gt -> gcdn n0 (sub a' b') b};
       XO b0 -> gcdn n0 a b0;
       XH -> XH};
     XO a0 ->
      case b of {
       XI p -> gcdn n0 a0 b;
       XO b0 -> XO (gcdn n0 a0 b0);
       XH -> XH};
     XH -> XH}}

gcd :: Positive -> Positive -> Positive
gcd a b =
  gcdn (plus (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Positive -> Positive -> Prod Positive
         (Prod Positive Positive)
ggcdn n a b =
  case n of {
   O -> Pair XH (Pair a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> Pair a (Pair XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           Pair g p ->
            case p of {
             Pair ba aa -> Pair g (Pair aa (add aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           Pair g p ->
            case p of {
             Pair ab bb -> Pair g (Pair (add bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair aa (XO bb))}};
       XH -> Pair XH (Pair a XH)};
     XO a0 ->
      case b of {
       XI p ->
        case ggcdn n0 a0 b of {
         Pair g p0 ->
          case p0 of {
           Pair aa bb -> Pair g (Pair (XO aa) bb)}};
       XO b0 ->
        case ggcdn n0 a0 b0 of {
         Pair g p -> Pair (XO g) p};
       XH -> Pair XH (Pair a XH)};
     XH -> Pair XH (Pair XH b)}}

ggcd :: Positive -> Positive -> Prod Positive (Prod Positive Positive)
ggcd a b =
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

lor :: Positive -> Positive -> Positive
lor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XI (lor p0 q0);
     XH -> p};
   XO p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XO (lor p0 q0);
     XH -> XI p0};
   XH ->
    case q of {
     XO q0 -> XI q0;
     _ -> q}}

land :: Positive -> Positive -> N
land p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> nsucc_double (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> Npos XH};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> N0};
   XH ->
    case q of {
     XO q0 -> N0;
     _ -> Npos XH}}

ldiff :: Positive -> Positive -> N
ldiff p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> nsucc_double (ldiff p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> ndouble (ldiff p0 q0);
     XH -> Npos p};
   XH ->
    case q of {
     XO q0 -> Npos XH;
     _ -> N0}}

lxor :: Positive -> Positive -> N
lxor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (lxor p0 q0);
     XO q0 -> nsucc_double (lxor p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> nsucc_double (lxor p0 q0);
     XO q0 -> ndouble (lxor p0 q0);
     XH -> Npos (XI p0)};
   XH ->
    case q of {
     XI q0 -> Npos (XO q0);
     XO q0 -> Npos (XI q0);
     XH -> N0}}

shiftl_nat :: Positive -> Nat -> Positive
shiftl_nat p n =
  nat_iter n (\x -> XO x) p

shiftr_nat :: Positive -> Nat -> Positive
shiftr_nat p n =
  nat_iter n div2 p

shiftl :: Positive -> N -> Positive
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 (\x -> XO x) p}

shiftr :: Positive -> N -> Positive
shiftr p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 div2 p}

testbit_nat :: Positive -> Nat -> Bool
testbit_nat p n =
  case p of {
   XI p0 ->
    case n of {
     O -> True;
     S n' -> testbit_nat p0 n'};
   XO p0 ->
    case n of {
     O -> False;
     S n' -> testbit_nat p0 n'};
   XH ->
    case n of {
     O -> True;
     S n0 -> False}}

testbit :: Positive -> N -> Bool
testbit p n =
  case p of {
   XI p0 ->
    case n of {
     N0 -> True;
     Npos n0 -> testbit p0 (pred_N n0)};
   XO p0 ->
    case n of {
     N0 -> False;
     Npos n0 -> testbit p0 (pred_N n0)};
   XH ->
    case n of {
     N0 -> True;
     Npos p0 -> False}}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op plus x (S O)

of_nat :: Nat -> Positive
of_nat n =
  case n of {
   O -> XH;
   S x ->
    case x of {
     O -> XH;
     S n0 -> succ (of_nat x)}}

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ (of_succ_nat x)}

eq_dec :: Positive -> Positive -> Sumbool
eq_dec x y =
  positive_rec (\p h y0 ->
    case y0 of {
     XI p0 -> sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0);
     _ -> Right}) (\p h y0 ->
    case y0 of {
     XO p0 -> sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0);
     _ -> Right}) (\y0 ->
    case y0 of {
     XH -> Left;
     _ -> Right}) x y

peano_rect :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rect a f p =
  let {f2 = peano_rect (f XH a) (\p0 x -> f (succ (XO p0)) (f (XO p0) x))} in
  case p of {
   XI q -> f (XO q) (f2 q);
   XO q -> f2 q;
   XH -> a}

peano_rec :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Positive PeanoView

peanoView_rect :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                  PeanoView -> a1
peanoView_rect f f0 p p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p1 p2 -> f0 p1 p2 (peanoView_rect f f0 p1 p2)}

peanoView_rec :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                 PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Positive -> PeanoView -> PeanoView
peanoView_xO p q =
  case q of {
   PeanoOne -> PeanoSucc XH PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc (succ (XO p0)) (PeanoSucc (XO p0)
    (peanoView_xO p0 q0))}

peanoView_xI :: Positive -> PeanoView -> PeanoView
peanoView_xI p q =
  case q of {
   PeanoOne -> PeanoSucc (succ XH) (PeanoSucc XH PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc (succ (XI p0)) (PeanoSucc (XI p0)
    (peanoView_xI p0 q0))}

peanoView :: Positive -> PeanoView
peanoView p =
  case p of {
   XI p0 -> peanoView_xI p0 (peanoView p0);
   XO p0 -> peanoView_xO p0 (peanoView p0);
   XH -> PeanoOne}

peanoView_iter :: a1 -> (Positive -> a1 -> a1) -> Positive -> PeanoView -> a1
peanoView_iter a f p q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Positive -> Positive -> Reflect
eqb_spec x y =
  iff_reflect (eqb x y)

switch_Eq :: Comparison -> Comparison -> Comparison
switch_Eq c c' =
  case c' of {
   Eq -> c;
   x -> x}

mask2cmp :: Mask -> Comparison
mask2cmp p =
  case p of {
   IsNul -> Eq;
   IsPos p0 -> Gt;
   IsNeg -> Lt}

leb_spec0 :: Positive -> Positive -> Reflect
leb_spec0 x y =
  iff_reflect (leb x y)

ltb_spec0 :: Positive -> Positive -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb x y)

max_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max n m) __ (hl __);
   _ -> compat m (max n m) __ (hr __)}

max_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: Positive -> Positive -> Sumbool
max_dec n m =
  max_case n m (\x y _ h0 -> h0) Left Right

min_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min n m) __ (hr __);
   _ -> compat n (min n m) __ (hl __)}

min_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: Positive -> Positive -> Sumbool
min_dec n m =
  min_case n m (\x y _ h0 -> h0) Left Right

max_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case0 :: Positive -> Positive -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: Positive -> Positive -> Sumbool
max_dec0 =
  max_dec

min_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case0 :: Positive -> Positive -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: Positive -> Positive -> Sumbool
min_dec0 =
  min_dec

type T0 = N

zero :: N
zero =
  N0

one :: N
one =
  Npos XH

two :: N
two =
  Npos (XO XH)

succ_double :: N -> N
succ_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

double :: N -> N
double n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

succ0 :: N -> N
succ0 n =
  case n of {
   N0 -> Npos XH;
   Npos p -> Npos (succ p)}

pred0 :: N -> N
pred0 n =
  case n of {
   N0 -> N0;
   Npos p -> pred_N p}

succ_pos :: N -> Positive
succ_pos n =
  case n of {
   N0 -> XH;
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

eqb0 :: N -> N -> Bool
eqb0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> True;
     Npos p -> False};
   Npos p ->
    case m of {
     N0 -> False;
     Npos q -> eqb p q}}

leb0 :: N -> N -> Bool
leb0 x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb0 :: N -> N -> Bool
ltb0 x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

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
    case p0 of {
     XI p -> Npos p;
     XO p -> Npos p;
     XH -> N0}}

even :: N -> Bool
even n =
  case n of {
   N0 -> True;
   Npos p ->
    case p of {
     XO p0 -> True;
     _ -> False}}

odd :: N -> Bool
odd n =
  negb (even n)

pow0 :: N -> N -> N
pow0 n p =
  case p of {
   N0 -> Npos XH;
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
    case p0 of {
     XI p -> Npos (size p);
     XO p -> Npos (size p);
     XH -> N0}}

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

pos_div_eucl :: Positive -> N -> Prod N N
pos_div_eucl a b =
  case a of {
   XI a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub0 r' b);
       False -> Pair (double q) r'}};
   XO a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub0 r' b);
       False -> Pair (double q) r'}};
   XH ->
    case b of {
     N0 -> Pair N0 (Npos XH);
     Npos p ->
      case p of {
       XH -> Pair (Npos XH) N0;
       _ -> Pair N0 (Npos XH)}}}

div_eucl :: N -> N -> Prod N N
div_eucl a b =
  case a of {
   N0 -> Pair N0 N0;
   Npos na ->
    case b of {
     N0 -> Pair N0 a;
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

ggcd0 :: N -> N -> Prod N (Prod N N)
ggcd0 a b =
  case a of {
   N0 -> Pair b (Pair N0 (Npos XH));
   Npos p ->
    case b of {
     N0 -> Pair a (Pair (Npos XH) N0);
     Npos q ->
      case ggcd p q of {
       Pair g p0 ->
        case p0 of {
         Pair aa bb -> Pair (Npos g) (Pair (Npos aa) (Npos bb))}}}}

sqrtrem0 :: N -> Prod N N
sqrtrem0 n =
  case n of {
   N0 -> Pair N0 N0;
   Npos p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair (Npos s) (Npos r);
       _ -> Pair (Npos s) N0}}}

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

testbit_nat0 :: N -> Nat -> Bool
testbit_nat0 a =
  case a of {
   N0 -> (\x -> False);
   Npos p -> testbit_nat p}

testbit0 :: N -> N -> Bool
testbit0 a n =
  case a of {
   N0 -> False;
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
iter0 n f x =
  case n of {
   N0 -> x;
   Npos p -> iter p f x}

eq_dec0 :: N -> N -> Sumbool
eq_dec0 n m =
  n_rec (\m0 ->
    case m0 of {
     N0 -> Left;
     Npos p -> Right}) (\p m0 ->
    case m0 of {
     N0 -> Right;
     Npos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0)}) n
    m

discr :: N -> Sumor Positive
discr n =
  case n of {
   N0 -> Inright;
   Npos p -> Inleft p}

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
leb_spec1 x y =
  iff_reflect (leb0 x y)

ltb_spec1 :: N -> N -> Reflect
ltb_spec1 x y =
  iff_reflect (ltb0 x y)

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
  case compare0 (Npos XH) a of {
   Lt -> succ0 (log2 (pred0 a));
   _ -> N0}

lcm :: N -> N -> N
lcm a b =
  mul0 a (div b (gcd0 a b))

eqb_spec0 :: N -> N -> Reflect
eqb_spec0 x y =
  iff_reflect (eqb0 x y)

b2n :: Bool -> N
b2n b =
  case b of {
   True -> Npos XH;
   False -> N0}

setbit :: N -> N -> N
setbit a n =
  lor0 a (shiftl0 (Npos XH) n)

clearbit :: N -> N -> N
clearbit a n =
  ldiff0 a (shiftl0 (Npos XH) n)

ones :: N -> N
ones n =
  pred0 (shiftl0 (Npos XH) n)

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
max_case1 n m x x0 x1 =
  max_case_strong1 n m x (\_ -> x0) (\_ -> x1)

max_dec1 :: N -> N -> Sumbool
max_dec1 n m =
  max_case1 n m (\x y _ h0 -> h0) Left Right

min_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

min_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case1 n m x x0 x1 =
  min_case_strong1 n m x (\_ -> x0) (\_ -> x1)

min_dec1 :: N -> N -> Sumbool
min_dec1 n m =
  min_case1 n m (\x y _ h0 -> h0) Left Right

max_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
max_case_strong2 n m x x0 =
  max_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case2 :: N -> N -> a1 -> a1 -> a1
max_case2 n m x x0 =
  max_case_strong2 n m (\_ -> x) (\_ -> x0)

max_dec2 :: N -> N -> Sumbool
max_dec2 =
  max_dec1

min_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
min_case_strong2 n m x x0 =
  min_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case2 :: N -> N -> a1 -> a1 -> a1
min_case2 n m x x0 =
  min_case_strong2 n m (\_ -> x) (\_ -> x0)

min_dec2 :: N -> N -> Sumbool
min_dec2 =
  min_dec1

pow_pos :: (a1 -> a1 -> a1) -> a1 -> Positive -> a1
pow_pos rmul x i =
  case i of {
   XI i0 -> let {p = pow_pos rmul x i0} in rmul x (rmul p p);
   XO i0 -> let {p = pow_pos rmul x i0} in rmul p p;
   XH -> x}

type T1 = Z

zero0 :: Z
zero0 =
  Z0

one0 :: Z
one0 =
  Zpos XH

two0 :: Z
two0 =
  Zpos (XO XH)

double0 :: Z -> Z
double0 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double0 :: Z -> Z
succ_double0 x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double0 (pos_sub p q);
     XO q -> succ_double0 (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double0 (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add1 :: Z -> Z -> Z
add1 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add x' y')}}

opp :: Z -> Z
opp x =
  case x of {
   Z0 -> Z0;
   Zpos x0 -> Zneg x0;
   Zneg x0 -> Zpos x0}

succ1 :: Z -> Z
succ1 x =
  add1 x (Zpos XH)

pred1 :: Z -> Z
pred1 x =
  add1 x (Zneg XH)

sub1 :: Z -> Z -> Z
sub1 m n =
  add1 m (opp n)

mul1 :: Z -> Z -> Z
mul1 x y =
  case x of {
   Z0 -> Z0;
   Zpos x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zpos (mul x' y');
     Zneg y' -> Zneg (mul x' y')};
   Zneg x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zneg (mul x' y');
     Zneg y' -> Zpos (mul x' y')}}

pow_pos0 :: Z -> Positive -> Z
pow_pos0 z n =
  iter n (mul1 z) (Zpos XH)

pow1 :: Z -> Z -> Z
pow1 x y =
  case y of {
   Z0 -> Zpos XH;
   Zpos p -> pow_pos0 x p;
   Zneg p -> Z0}

square1 :: Z -> Z
square1 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (square p);
   Zneg p -> Zpos (square p)}

compare1 :: Z -> Z -> Comparison
compare1 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> Eq;
     Zpos y' -> Lt;
     Zneg y' -> Gt};
   Zpos x' ->
    case y of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

sgn :: Z -> Z
sgn z =
  case z of {
   Z0 -> Z0;
   Zpos p -> Zpos XH;
   Zneg p -> Zneg XH}

leb1 :: Z -> Z -> Bool
leb1 x y =
  case compare1 x y of {
   Gt -> False;
   _ -> True}

ltb1 :: Z -> Z -> Bool
ltb1 x y =
  case compare1 x y of {
   Lt -> True;
   _ -> False}

geb :: Z -> Z -> Bool
geb x y =
  case compare1 x y of {
   Lt -> False;
   _ -> True}

gtb :: Z -> Z -> Bool
gtb x y =
  case compare1 x y of {
   Gt -> True;
   _ -> False}

eqb1 :: Z -> Z -> Bool
eqb1 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> True;
     _ -> False};
   Zpos p ->
    case y of {
     Zpos q -> eqb p q;
     _ -> False};
   Zneg p ->
    case y of {
     Zneg q -> eqb p q;
     _ -> False}}

max1 :: Z -> Z -> Z
max1 n m =
  case compare1 n m of {
   Lt -> m;
   _ -> n}

min1 :: Z -> Z -> Z
min1 n m =
  case compare1 n m of {
   Gt -> m;
   _ -> n}

abs :: Z -> Z
abs z =
  case z of {
   Zneg p -> Zpos p;
   x -> x}

abs_nat :: Z -> Nat
abs_nat z =
  case z of {
   Z0 -> O;
   Zpos p -> to_nat p;
   Zneg p -> to_nat p}

abs_N :: Z -> N
abs_N z =
  case z of {
   Z0 -> N0;
   Zpos p -> Npos p;
   Zneg p -> Npos p}

to_nat1 :: Z -> Nat
to_nat1 z =
  case z of {
   Zpos p -> to_nat p;
   _ -> O}

to_N :: Z -> N
to_N z =
  case z of {
   Zpos p -> Npos p;
   _ -> N0}

of_nat1 :: Nat -> Z
of_nat1 n =
  case n of {
   O -> Z0;
   S n0 -> Zpos (of_succ_nat n0)}

of_N :: N -> Z
of_N n =
  case n of {
   N0 -> Z0;
   Npos p -> Zpos p}

to_pos :: Z -> Positive
to_pos z =
  case z of {
   Zpos p -> p;
   _ -> XH}

iter1 :: Z -> (a1 -> a1) -> a1 -> a1
iter1 n f x =
  case n of {
   Zpos p -> iter p f x;
   _ -> x}

pos_div_eucl0 :: Positive -> Z -> Prod Z Z
pos_div_eucl0 a b =
  case a of {
   XI a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = add1 (mul1 (Zpos (XO XH)) r) (Zpos XH)} in
      case ltb1 r' b of {
       True -> Pair (mul1 (Zpos (XO XH)) q) r';
       False -> Pair (add1 (mul1 (Zpos (XO XH)) q) (Zpos XH)) (sub1 r' b)}};
   XO a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = mul1 (Zpos (XO XH)) r} in
      case ltb1 r' b of {
       True -> Pair (mul1 (Zpos (XO XH)) q) r';
       False -> Pair (add1 (mul1 (Zpos (XO XH)) q) (Zpos XH)) (sub1 r' b)}};
   XH ->
    case leb1 (Zpos (XO XH)) b of {
     True -> Pair Z0 (Zpos XH);
     False -> Pair (Zpos XH) Z0}}

div_eucl0 :: Z -> Z -> Prod Z Z
div_eucl0 a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos p -> pos_div_eucl0 a' b;
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add1 q (Zpos XH))) (add1 b r)}}};
   Zneg a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos p ->
      case pos_div_eucl0 a' b of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add1 q (Zpos XH))) (sub1 b r)}};
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       Pair q r -> Pair q (opp r)}}}

div1 :: Z -> Z -> Z
div1 a b =
  case div_eucl0 a b of {
   Pair q x -> q}

modulo0 :: Z -> Z -> Z
modulo0 a b =
  case div_eucl0 a b of {
   Pair x r -> r}

quotrem :: Z -> Z -> Prod Z Z
quotrem a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a0 ->
    case b of {
     Z0 -> Pair Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (of_N r)};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (of_N r)}};
   Zneg a0 ->
    case b of {
     Z0 -> Pair Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (opp (of_N r))};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (opp (of_N r))}}}

quot :: Z -> Z -> Z
quot a b =
  fst (quotrem a b)

rem :: Z -> Z -> Z
rem a b =
  snd (quotrem a b)

even0 :: Z -> Bool
even0 z =
  case z of {
   Z0 -> True;
   Zpos p ->
    case p of {
     XO p0 -> True;
     _ -> False};
   Zneg p ->
    case p of {
     XO p0 -> True;
     _ -> False}}

odd0 :: Z -> Bool
odd0 z =
  case z of {
   Z0 -> False;
   Zpos p ->
    case p of {
     XO p0 -> False;
     _ -> True};
   Zneg p ->
    case p of {
     XO p0 -> False;
     _ -> True}}

div3 :: Z -> Z
div3 z =
  case z of {
   Z0 -> Z0;
   Zpos p ->
    case p of {
     XH -> Z0;
     _ -> Zpos (div2 p)};
   Zneg p -> Zneg (div2_up p)}

quot2 :: Z -> Z
quot2 z =
  case z of {
   Z0 -> Z0;
   Zpos p ->
    case p of {
     XH -> Z0;
     _ -> Zpos (div2 p)};
   Zneg p ->
    case p of {
     XH -> Z0;
     _ -> Zneg (div2 p)}}

log0 :: Z -> Z
log0 z =
  case z of {
   Zpos p0 ->
    case p0 of {
     XI p -> Zpos (size p);
     XO p -> Zpos (size p);
     XH -> Z0};
   _ -> Z0}

sqrtrem1 :: Z -> Prod Z Z
sqrtrem1 n =
  case n of {
   Zpos p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair (Zpos s) (Zpos r);
       _ -> Pair (Zpos s) Z0}};
   _ -> Pair Z0 Z0}

sqrt1 :: Z -> Z
sqrt1 n =
  case n of {
   Zpos p -> Zpos (sqrt p);
   _ -> Z0}

gcd1 :: Z -> Z -> Z
gcd1 a b =
  case a of {
   Z0 -> abs b;
   Zpos a0 ->
    case b of {
     Z0 -> abs a;
     Zpos b0 -> Zpos (gcd a0 b0);
     Zneg b0 -> Zpos (gcd a0 b0)};
   Zneg a0 ->
    case b of {
     Z0 -> abs a;
     Zpos b0 -> Zpos (gcd a0 b0);
     Zneg b0 -> Zpos (gcd a0 b0)}}

ggcd1 :: Z -> Z -> Prod Z (Prod Z Z)
ggcd1 a b =
  case a of {
   Z0 -> Pair (abs b) (Pair Z0 (sgn b));
   Zpos a0 ->
    case b of {
     Z0 -> Pair (abs a) (Pair (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zpos aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zpos aa) (Zneg bb))}}};
   Zneg a0 ->
    case b of {
     Z0 -> Pair (abs a) (Pair (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zneg aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zneg aa) (Zneg bb))}}}}

testbit1 :: Z -> Z -> Bool
testbit1 a n =
  case n of {
   Z0 -> odd0 a;
   Zpos p ->
    case a of {
     Z0 -> False;
     Zpos a0 -> testbit a0 (Npos p);
     Zneg a0 -> negb (testbit0 (pred_N a0) (Npos p))};
   Zneg p -> False}

shiftl1 :: Z -> Z -> Z
shiftl1 a n =
  case n of {
   Z0 -> a;
   Zpos p -> iter p (mul1 (Zpos (XO XH))) a;
   Zneg p -> iter p div3 a}

shiftr1 :: Z -> Z -> Z
shiftr1 a n =
  shiftl1 a (opp n)

lor1 :: Z -> Z -> Z
lor1 a b =
  case a of {
   Z0 -> b;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zpos (lor a0 b0);
     Zneg b0 -> Zneg (succ_pos (ldiff0 (pred_N b0) (Npos a0)))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (ldiff0 (pred_N a0) (Npos b0)));
     Zneg b0 -> Zneg (succ_pos (land0 (pred_N a0) (pred_N b0)))}}

land1 :: Z -> Z -> Z
land1 a b =
  case a of {
   Z0 -> Z0;
   Zpos a0 ->
    case b of {
     Z0 -> Z0;
     Zpos b0 -> of_N (land a0 b0);
     Zneg b0 -> of_N (ldiff0 (Npos a0) (pred_N b0))};
   Zneg a0 ->
    case b of {
     Z0 -> Z0;
     Zpos b0 -> of_N (ldiff0 (Npos b0) (pred_N a0));
     Zneg b0 -> Zneg (succ_pos (lor0 (pred_N a0) (pred_N b0)))}}

ldiff1 :: Z -> Z -> Z
ldiff1 a b =
  case a of {
   Z0 -> Z0;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> of_N (ldiff a0 b0);
     Zneg b0 -> of_N (land0 (Npos a0) (pred_N b0))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (lor0 (pred_N a0) (Npos b0)));
     Zneg b0 -> of_N (ldiff0 (pred_N b0) (pred_N a0))}}

lxor1 :: Z -> Z -> Z
lxor1 a b =
  case a of {
   Z0 -> b;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> of_N (lxor a0 b0);
     Zneg b0 -> Zneg (succ_pos (lxor0 (Npos a0) (pred_N b0)))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (lxor0 (pred_N a0) (Npos b0)));
     Zneg b0 -> of_N (lxor0 (pred_N a0) (pred_N b0))}}

eq_dec1 :: Z -> Z -> Sumbool
eq_dec1 x y =
  z_rec (\y0 ->
    case y0 of {
     Z0 -> Left;
     _ -> Right}) (\p y0 ->
    case y0 of {
     Zpos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0);
     _ -> Right}) (\p y0 ->
    case y0 of {
     Zneg p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0);
     _ -> Right}) x y

leb_spec2 :: Z -> Z -> Reflect
leb_spec2 x y =
  iff_reflect (leb1 x y)

ltb_spec2 :: Z -> Z -> Reflect
ltb_spec2 x y =
  iff_reflect (ltb1 x y)

sqrt_up0 :: Z -> Z
sqrt_up0 a =
  case compare1 Z0 a of {
   Lt -> succ1 (sqrt1 (pred1 a));
   _ -> Z0}

log2_up0 :: Z -> Z
log2_up0 a =
  case compare1 (Zpos XH) a of {
   Lt -> succ1 (log0 (pred1 a));
   _ -> Z0}

div4 :: Z -> Z -> Z
div4 =
  quot

modulo1 :: Z -> Z -> Z
modulo1 =
  rem

lcm0 :: Z -> Z -> Z
lcm0 a b =
  abs (mul1 a (div1 b (gcd1 a b)))

eqb_spec1 :: Z -> Z -> Reflect
eqb_spec1 x y =
  iff_reflect (eqb1 x y)

b2z :: Bool -> Z
b2z b =
  case b of {
   True -> Zpos XH;
   False -> Z0}

setbit0 :: Z -> Z -> Z
setbit0 a n =
  lor1 a (shiftl1 (Zpos XH) n)

clearbit0 :: Z -> Z -> Z
clearbit0 a n =
  ldiff1 a (shiftl1 (Zpos XH) n)

lnot0 :: Z -> Z
lnot0 a =
  pred1 (opp a)

ones0 :: Z -> Z
ones0 n =
  pred1 (shiftl1 (Zpos XH) n)

max_case_strong3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat n (max1 n m) __ (hl __);
   _ -> compat m (max1 n m) __ (hr __)}

max_case3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case3 n m x x0 x1 =
  max_case_strong3 n m x (\_ -> x0) (\_ -> x1)

max_dec3 :: Z -> Z -> Sumbool
max_dec3 n m =
  max_case3 n m (\x y _ h0 -> h0) Left Right

min_case_strong3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat m (min1 n m) __ (hr __);
   _ -> compat n (min1 n m) __ (hl __)}

min_case3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case3 n m x x0 x1 =
  min_case_strong3 n m x (\_ -> x0) (\_ -> x1)

min_dec3 :: Z -> Z -> Sumbool
min_dec3 n m =
  min_case3 n m (\x y _ h0 -> h0) Left Right

max_case_strong4 :: Z -> Z -> (() -> a1) -> (() -> a1) -> a1
max_case_strong4 n m x x0 =
  max_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case4 :: Z -> Z -> a1 -> a1 -> a1
max_case4 n m x x0 =
  max_case_strong4 n m (\_ -> x) (\_ -> x0)

max_dec4 :: Z -> Z -> Sumbool
max_dec4 =
  max_dec3

min_case_strong4 :: Z -> Z -> (() -> a1) -> (() -> a1) -> a1
min_case_strong4 n m x x0 =
  min_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case4 :: Z -> Z -> a1 -> a1 -> a1
min_case4 n m x x0 =
  min_case_strong4 n m (\_ -> x) (\_ -> x0)

min_dec4 :: Z -> Z -> Sumbool
min_dec4 =
  min_dec3

data Q =
   Qmake Z Positive

qnum :: Q -> Z
qnum q =
  case q of {
   Qmake qnum0 qden0 -> qnum0}

qden :: Q -> Positive
qden q =
  case q of {
   Qmake qnum0 qden0 -> qden0}

inject_Z :: Z -> Q
inject_Z x =
  Qmake x XH

qcompare :: Q -> Q -> Comparison
qcompare p q =
  compare1 (mul1 (qnum p) (Zpos (qden q))) (mul1 (qnum q) (Zpos (qden p)))

qeq_dec :: Q -> Q -> Sumbool
qeq_dec x y =
  eq_dec1 (mul1 (qnum x) (Zpos (qden y))) (mul1 (qnum y) (Zpos (qden x)))

qplus :: Q -> Q -> Q
qplus x y =
  Qmake
    (add1 (mul1 (qnum x) (Zpos (qden y))) (mul1 (qnum y) (Zpos (qden x))))
    (mul (qden x) (qden y))

qmult :: Q -> Q -> Q
qmult x y =
  Qmake (mul1 (qnum x) (qnum y)) (mul (qden x) (qden y))

qopp :: Q -> Q
qopp x =
  Qmake (opp (qnum x)) (qden x)

qminus :: Q -> Q -> Q
qminus x y =
  qplus x (qopp y)

qinv :: Q -> Q
qinv x =
  case qnum x of {
   Z0 -> Qmake Z0 XH;
   Zpos p -> Qmake (Zpos (qden x)) p;
   Zneg p -> Qmake (Zneg (qden x)) p}

qdiv :: Q -> Q -> Q
qdiv x y =
  qmult x (qinv y)

qpower_positive :: Q -> Positive -> Q
qpower_positive q p =
  pow_pos qmult q p

qpower :: Q -> Z -> Q
qpower q z =
  case z of {
   Z0 -> Qmake (Zpos XH) XH;
   Zpos p -> qpower_positive q p;
   Zneg p -> qinv (qpower_positive q p)}

qred :: Q -> Q
qred q =
  case q of {
   Qmake q1 q2 ->
    case snd (ggcd1 q1 (Zpos q2)) of {
     Pair r1 r2 -> Qmake r1 (to_pos r2)}}

qminus' :: Q -> Q -> Q
qminus' x y =
  qred (qminus x y)

qfloor :: Q -> Z
qfloor x =
  case x of {
   Qmake n d -> div1 n (Zpos d)}

qceiling :: Q -> Z
qceiling x =
  opp (qfloor (qopp x))

type Csymmetric a r = a -> a -> r -> r

data Stream a =
   Cons a (Stream a)

hd :: (Stream a1) -> a1
hd x =
  case x of {
   Cons a s -> a}

tl :: (Stream a1) -> Stream a1
tl x =
  case x of {
   Cons a s -> s}

map :: (a1 -> a2) -> (Stream a1) -> Stream a2
map f s =
  Cons (f (hd s)) (map f (tl s))

zipWith :: (a1 -> a2 -> a3) -> (Stream a1) -> (Stream a2) -> Stream a3
zipWith f a b =
  Cons (f (hd a) (hd b)) (zipWith f (tl a) (tl b))

type Cast a b = a -> b

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

data RSetoid =
   Build_RSetoid

type St_car = ()

ap_Q_cotransitive0 :: Q -> Q -> Q -> Sum () ()
ap_Q_cotransitive0 x y z =
  case qeq_dec x z of {
   Left -> Inr __;
   Right -> Inl __}

type Cotransitive a r = a -> a -> r -> a -> Sum r r

data Is_CSetoid a ap =
   Build_is_CSetoid (Csymmetric a ap) (Cotransitive a ap)

data CSetoid =
   MakeCSetoid RSetoid (Is_CSetoid St_car ())

cs_crr :: CSetoid -> RSetoid
cs_crr c =
  case c of {
   MakeCSetoid cs_crr0 cs_proof -> cs_crr0}

build_CSetoid :: (Is_CSetoid a1 a2) -> CSetoid
build_CSetoid p =
  MakeCSetoid Build_RSetoid (unsafeCoerce p)

ap_Q_cotransitive1 :: Q -> Q -> Q -> Sum () ()
ap_Q_cotransitive1 x y z =
  ap_Q_cotransitive0 x y z

ap_Q_is_apartness :: Is_CSetoid Q ()
ap_Q_is_apartness =
  Build_is_CSetoid __ (\x x0 _ -> ap_Q_cotransitive1 x x0)

q_as_CSetoid :: CSetoid
q_as_CSetoid =
  build_CSetoid ap_Q_is_apartness

q_is_Setoid :: RSetoid
q_is_Setoid =
  cs_crr q_as_CSetoid

type Qpos = Q

qposMake :: Positive -> Positive -> Qpos
qposMake num den =
  Qmake (Zpos num) den

qposAsQ :: Qpos -> Q
qposAsQ =
  proj1_sig

mkQpos :: Q -> Qpos
mkQpos a =
  a

qpos_mult :: Qpos -> Qpos -> Qpos
qpos_mult x y =
  qmult (qposAsQ x) (qposAsQ y)

qpos_inv :: Qpos -> Qpos
qpos_inv x =
  qinv (qposAsQ x)

qpos_power :: Qpos -> Z -> Qpos
qpos_power x z =
  mkQpos (qpower (qposAsQ x) z)

min2 :: (a1 -> a1 -> Sumbool) -> a1 -> a1 -> a1
min2 le_total x y =
  case le_total x y of {
   Left -> x;
   Right -> y}

min_case5 :: (a1 -> a1 -> Sumbool) -> a1 -> a1 -> (() -> a2) -> (() -> a2) ->
             a2
min_case5 le_total x y hx hy =
  case le_total x y of {
   Left -> hx __;
   Right -> hy __}

max2 :: (a1 -> a1 -> Sumbool) -> a1 -> a1 -> a1
max2 le_total x y =
  case le_total y x of {
   Left -> x;
   Right -> y}

max_case5 :: (a1 -> a1 -> Sumbool) -> a1 -> a1 -> (() -> a2) -> (() -> a2) ->
             a2
max_case5 le_total x y x0 x1 =
  let {flip_le_total = \x2 y0 -> le_total y0 x2} in
  min_case5 flip_le_total x y x0 x1

qlt_le_dec_fast :: Q -> Q -> Sumbool
qlt_le_dec_fast x y =
  let {c = qcompare x y} in
  case c of {
   Lt -> Left;
   _ -> Right}

qle_total :: Q -> Q -> Sumbool
qle_total x y =
  qlt_le_dec_fast x y

qmin :: Q -> Q -> Q
qmin =
  min2 qle_total

qmax :: Q -> Q -> Q
qmax =
  max2 qle_total

data QposInf =
   Qpos2QposInf Qpos
 | QposInfinity

qposInf_bind :: (Qpos -> QposInf) -> QposInf -> QposInf
qposInf_bind f x =
  case x of {
   Qpos2QposInf x' -> f x';
   QposInfinity -> QposInfinity}

qposInf_mult :: QposInf -> QposInf -> QposInf
qposInf_mult x y =
  qposInf_bind (\x' ->
    qposInf_bind (\y' -> Qpos2QposInf (qpos_mult x' y')) y) x

type MetricSpace =
  RSetoid
  -- singleton inductive, whose constructor was Build_MetricSpace
  
ball_ex_dec :: MetricSpace -> (Qpos -> St_car -> St_car -> Sumbool) ->
               QposInf -> St_car -> St_car -> Sumbool
ball_ex_dec x ball_dec e a b =
  case e of {
   Qpos2QposInf e0 -> ball_dec e0 a b;
   QposInfinity -> Left}

data UniformlyContinuousFunction =
   Build_UniformlyContinuousFunction (St_car -> St_car) (Qpos -> QposInf)

ucFun :: MetricSpace -> MetricSpace -> UniformlyContinuousFunction -> St_car
         -> St_car
ucFun x y u =
  case u of {
   Build_UniformlyContinuousFunction ucFun0 mu0 -> ucFun0}

mu :: MetricSpace -> MetricSpace -> UniformlyContinuousFunction -> Qpos ->
      QposInf
mu x y u =
  case u of {
   Build_UniformlyContinuousFunction ucFun0 mu0 -> mu0}

uc_compose :: MetricSpace -> MetricSpace -> MetricSpace -> St_car -> St_car
              -> St_car
uc_compose x y z g f =
  unsafeCoerce (Build_UniformlyContinuousFunction (\x0 ->
    ucFun y z (unsafeCoerce g) (ucFun x y (unsafeCoerce f) x0)) (\e ->
    qposInf_bind (mu x y (unsafeCoerce f)) (mu y z (unsafeCoerce g) e)))

type DecidableMetric = Qpos -> St_car -> St_car -> Sumbool

type RegularFunction =
  QposInf -> St_car
  -- singleton inductive, whose constructor was Build_RegularFunction
  
approximate :: MetricSpace -> RegularFunction -> QposInf -> St_car
approximate x r =
  r

regFun_Setoid :: MetricSpace -> RSetoid
regFun_Setoid x =
  Build_RSetoid

complete :: MetricSpace -> MetricSpace
complete x =
  regFun_Setoid x

cunit_fun :: MetricSpace -> St_car -> St_car
cunit_fun x x0 =
  unsafeCoerce (\x1 -> x0)

cunit :: MetricSpace -> St_car
cunit x =
  unsafeCoerce (Build_UniformlyContinuousFunction (cunit_fun x) (\x0 ->
    Qpos2QposInf x0))

cjoin_raw :: MetricSpace -> St_car -> QposInf -> St_car
cjoin_raw x x0 e =
  approximate x
    (unsafeCoerce
      (approximate (complete x) (unsafeCoerce x0)
        (qposInf_mult (Qpos2QposInf (qposMake XH (XO XH))) e)))
    (qposInf_mult (Qpos2QposInf (qposMake XH (XO XH))) e)

cjoin_fun :: MetricSpace -> St_car -> St_car
cjoin_fun x x0 =
  unsafeCoerce (cjoin_raw x x0)

cjoin :: MetricSpace -> St_car
cjoin x =
  unsafeCoerce (Build_UniformlyContinuousFunction (cjoin_fun x) (\x0 ->
    Qpos2QposInf x0))

cmap_fun :: MetricSpace -> MetricSpace -> St_car -> St_car -> St_car
cmap_fun x y f x0 =
  unsafeCoerce (\e ->
    ucFun x y (unsafeCoerce f)
      (approximate x (unsafeCoerce x0)
        (qposInf_bind (mu x y (unsafeCoerce f)) e)))

cmap :: MetricSpace -> MetricSpace -> St_car -> St_car
cmap x y f =
  unsafeCoerce (Build_UniformlyContinuousFunction (cmap_fun x y f)
    (mu x y (unsafeCoerce f)))

cbind :: MetricSpace -> MetricSpace -> St_car -> St_car
cbind x y f =
  uc_compose (complete x) (complete (complete y)) (complete y) (cjoin y)
    (cmap x (complete y) f)

q_as_MetricSpace :: MetricSpace
q_as_MetricSpace =
  q_is_Setoid

qmetric_dec :: DecidableMetric
qmetric_dec e a b =
  let {c = qopp (qposAsQ e)} in
  let {d = qminus (unsafeCoerce a) (unsafeCoerce b)} in
  let {s = qlt_le_dec_fast d c} in
  case s of {
   Left -> Right;
   Right ->
    let {s0 = qlt_le_dec_fast (qposAsQ e) d} in
    case s0 of {
     Left -> Right;
     Right -> Left}}

qball_ex_bool :: QposInf -> St_car -> St_car -> Bool
qball_ex_bool e a b =
  case ball_ex_dec q_as_MetricSpace qmetric_dec e a b of {
   Left -> True;
   Right -> False}

q_0 :: Zero Q
q_0 =
  Qmake Z0 XH

q_1 :: One Q
q_1 =
  Qmake (Zpos XH) XH

q_plus :: Plus Q
q_plus =
  qplus

q_mult :: Mult Q
q_mult =
  qmult

cR :: MetricSpace
cR =
  complete q_as_MetricSpace

inject_Q_CR :: Cast Q St_car
inject_Q_CR =
  unsafeCoerce
    (ucFun q_as_MetricSpace (complete q_as_MetricSpace)
      (unsafeCoerce (cunit q_as_MetricSpace)))

qboundBelow_uc :: St_car -> St_car
qboundBelow_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce (qmax (unsafeCoerce a) (unsafeCoerce b))) (\x ->
    Qpos2QposInf x))

qboundAbove_uc :: St_car -> St_car
qboundAbove_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce (qmin (unsafeCoerce a) (unsafeCoerce b))) (\x ->
    Qpos2QposInf x))

qscale_modulus :: Q -> Qpos -> QposInf
qscale_modulus a e =
  case a of {
   Qmake qnum0 ad ->
    case qnum0 of {
     Z0 -> QposInfinity;
     Zpos an -> Qpos2QposInf (qpos_mult (qposMake ad an) e);
     Zneg an -> Qpos2QposInf (qpos_mult (qposMake ad an) e)}}

qboundAbs :: Qpos -> St_car
qboundAbs c =
  uc_compose q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace
    (qboundBelow_uc (unsafeCoerce (qopp (qposAsQ c))))
    (qboundAbove_uc (unsafeCoerce (qposAsQ c)))

qinv_modulus :: Qpos -> Qpos -> Qpos
qinv_modulus c e =
  qpos_mult (qpos_mult c c) e

qinv_pos_uc :: Qpos -> St_car
qinv_pos_uc c =
  unsafeCoerce (Build_UniformlyContinuousFunction (\a ->
    unsafeCoerce (qinv (qmax (qposAsQ c) (unsafeCoerce a)))) (\e ->
    Qpos2QposInf (qinv_modulus c e)))

cRinv_pos :: Qpos -> St_car
cRinv_pos c =
  cmap q_as_MetricSpace q_as_MetricSpace (qinv_pos_uc c)

approximateQ :: Q -> Positive -> Q
approximateQ x p =
  case x of {
   Qmake n d -> Qmake (div1 (mul1 n (Zpos p)) (Zpos d)) p}

compress_raw :: St_car -> QposInf -> Q
compress_raw x e =
  case e of {
   Qpos2QposInf e0 ->
    case qposAsQ e0 of {
     Qmake n d ->
      case succ1 (div1 (mul1 (Zpos (XO XH)) (Zpos d)) n) of {
       Zpos p ->
        approximateQ
          (unsafeCoerce
            (approximate q_as_MetricSpace (unsafeCoerce x) (Qpos2QposInf
              (qposMake XH p)))) p;
       _ ->
        unsafeCoerce
          (approximate q_as_MetricSpace (unsafeCoerce x) (Qpos2QposInf e0))}};
   QposInfinity ->
    unsafeCoerce (approximate q_as_MetricSpace (unsafeCoerce x) e)}

compress_fun :: St_car -> St_car
compress_fun x =
  unsafeCoerce (unsafeCoerce (compress_raw x))

compress :: St_car
compress =
  unsafeCoerce (Build_UniformlyContinuousFunction compress_fun (\x ->
    Qpos2QposInf x))

qpower_N_modulus :: N -> Qpos -> Qpos -> QposInf
qpower_N_modulus n c e =
  case n of {
   N0 -> QposInfinity;
   Npos p -> Qpos2QposInf
    (qpos_mult e
      (qpos_inv (qpos_mult (qposMake p XH) (qpos_power c (pred1 (Zpos p))))))}

qpower_N_uc :: N -> Qpos -> St_car
qpower_N_uc n c =
  unsafeCoerce (Build_UniformlyContinuousFunction (\x ->
    unsafeCoerce
      (qpower
        (unsafeCoerce
          (ucFun q_as_MetricSpace q_as_MetricSpace
            (unsafeCoerce (qboundAbs c)) x)) (of_N n)))
    (qpower_N_modulus n c))

cRpower_N_bounded :: N -> Qpos -> St_car
cRpower_N_bounded n c =
  cmap q_as_MetricSpace q_as_MetricSpace (qpower_N_uc n c)

iterate :: (a1 -> a1) -> a1 -> Stream a1
iterate f x =
  Cons x (iterate f (f x))

takeUntil :: ((Stream a1) -> Bool) -> (Stream a1) -> (a1 -> a2 -> a2) -> a2
             -> a2
takeUntil p s cons nil =
  case p s of {
   True -> nil;
   False -> cons (hd s) (takeUntil p (tl s) cons nil)}

mult_Streams :: (Mult a1) -> (Stream a1) -> (Stream a1) -> Stream a1
mult_Streams h1 =
  zipWith (mult h1)

powers_help :: (Mult a1) -> a1 -> a1 -> Stream a1
powers_help h1 a =
  iterate (\y -> mult h1 y a)

powers :: (Mult a1) -> (One a1) -> a1 -> Stream a1
powers h1 h3 a =
  powers_help h1 a (one1 h3)

partialAlternatingSumUntil :: ((Stream Q) -> Bool) -> (Stream Q) -> Q
partialAlternatingSumUntil p s =
  takeUntil p s qminus' (zero1 q_0)

infiniteAlternatingSum_raw :: (Stream Q) -> QposInf -> Q
infiniteAlternatingSum_raw s __U03b5_ =
  partialAlternatingSumUntil (\s0 ->
    qball_ex_bool __U03b5_ (hd (unsafeCoerce s0))
      (unsafeCoerce (Qmake Z0 XH))) s

infiniteAlternatingSum :: (Stream Q) -> St_car
infiniteAlternatingSum seq =
  unsafeCoerce (unsafeCoerce (infiniteAlternatingSum_raw seq))

pfactorials_help :: Positive -> Positive -> Stream Positive
pfactorials_help n c =
  Cons c (pfactorials_help (succ n) (mul n c))

pfactorials :: Stream Positive
pfactorials =
  pfactorials_help XH XH

qrecip_factorials :: Stream Q
qrecip_factorials =
  map (\x -> Qmake (Zpos XH) x) pfactorials

expSequence :: Q -> Stream Q
expSequence a =
  mult_Streams q_mult qrecip_factorials (powers q_mult q_1 a)

rational_exp_small_neg :: Q -> St_car
rational_exp_small_neg a =
  infiniteAlternatingSum (expSequence (qopp a))

rational_exp_neg_bounded :: Nat -> Q -> St_car
rational_exp_neg_bounded n a =
  case n of {
   O -> rational_exp_small_neg a;
   S n' ->
    case qlt_le_dec_fast a (qopp (Qmake (Zpos XH) XH)) of {
     Left ->
      ucFun cR cR
        (unsafeCoerce (cRpower_N_bounded (Npos (XO XH)) (qposMake XH XH)))
        (ucFun cR cR (unsafeCoerce compress)
          (rational_exp_neg_bounded n'
            (qdiv a (plus0 q_plus (one1 q_1) (one1 q_1)))));
     Right -> rational_exp_small_neg a}}

rational_exp_neg :: Q -> St_car
rational_exp_neg a =
  rational_exp_neg_bounded
    (case qnum a of {
      Z0 -> O;
      Zpos x -> size_nat x;
      Zneg x -> size_nat x}) a

rational_exp :: Q -> St_car
rational_exp a =
  let {s = qle_total (Qmake Z0 XH) a} in
  case s of {
   Left ->
    ucFun cR cR
      (unsafeCoerce
        (cRinv_pos (qpos_power (qposMake XH (XI XH)) (qceiling a))))
      (rational_exp_neg (qopp a));
   Right -> rational_exp_neg a}

exp_bound :: Z -> Qpos
exp_bound z =
  case z of {
   Z0 -> qposMake XH XH;
   Zpos p -> qpos_power (qposMake (XI XH) XH) (Zpos p);
   Zneg p -> qpos_power (qposMake XH (XO XH)) (Zpos p)}

exp_bound_uc :: Z -> St_car
exp_bound_uc z =
  unsafeCoerce (Build_UniformlyContinuousFunction (\a ->
    rational_exp (qmin (inject_Z z) (unsafeCoerce a)))
    (qscale_modulus (qposAsQ (exp_bound z))))

exp_bounded :: Z -> St_car
exp_bounded z =
  cbind q_as_MetricSpace q_as_MetricSpace (exp_bound_uc z)

exp :: St_car -> St_car
exp x =
  ucFun cR cR
    (unsafeCoerce
      (exp_bounded
        (qceiling
          (qplus
            (unsafeCoerce
              (approximate q_as_MetricSpace (unsafeCoerce x) (Qpos2QposInf
                (qposMake XH XH)))) (Qmake (Zpos XH) XH))))) x

answer :: Positive -> St_car -> Z
answer n r =
  let {m = iter n (mul (XO (XI (XO XH)))) XH} in
  case qmult
         (unsafeCoerce
           (approximate q_as_MetricSpace (unsafeCoerce r) (Qpos2QposInf
             (qposMake XH m)))) (inject_Z (Zpos m)) of {
   Qmake a b -> div1 a (Zpos b)}

test :: Z
test =
  answer ((XI (XI XH))) (exp (inject_Q_CR (Qmake (Zpos XH) XH)))

{-the code below was manually written, not extracted from Coq-}
pos2Int :: Positive -> Prelude.Integer
pos2Int XH = 1
pos2Int (XO p) = (Prelude.+) (pos2Int p)  (pos2Int p)
pos2Int (XI p) = (Prelude.+) (pos2Int p)  ((Prelude.+) (pos2Int p) 1)


toInt :: Z -> Prelude.Integer
toInt Z0 = 0
toInt (Zpos p) = pos2Int p
toInt (Zneg p) = (Prelude.negate) (pos2Int p)


{- main = Prelude.print (toInt Z0) ; this worked-}
main = Prelude.print (toInt test)

