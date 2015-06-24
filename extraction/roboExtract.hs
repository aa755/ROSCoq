{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module RoboExtract where

import qualified Prelude


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
   Npos x0 -> f0 x0}

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
   Zpos x0 -> f0 x0;
   Zneg x0 -> f1 x0}

z_rec :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rec =
  z_rect

type T = Positive

succ :: Positive -> Positive
succ x0 =
  case x0 of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x0 y0 =
  case x0 of {
   XI p ->
    case y0 of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y0 of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH ->
    case y0 of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x0 y0 =
  case x0 of {
   XI p ->
    case y0 of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y0 of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH ->
    case y0 of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x0 =
  case x0 of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

pred :: Positive -> Positive
pred x0 =
  case x0 of {
   XI p -> XO p;
   XO p -> pred_double p;
   XH -> XH}

pred_N :: Positive -> N
pred_N x0 =
  case x0 of {
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
   IsPos x0 -> f0 x0;
   IsNeg -> f1}

mask_rec :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x0 =
  case x0 of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x0 =
  case x0 of {
   IsPos p -> IsPos (XO p);
   x1 -> x1}

double_pred_mask :: Positive -> Mask
double_pred_mask x0 =
  case x0 of {
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
sub_mask x0 y0 =
  case x0 of {
   XI p ->
    case y0 of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y0 of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH ->
    case y0 of {
     XH -> IsNul;
     _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x0 y0 =
  case x0 of {
   XI p ->
    case y0 of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y0 of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x0 y0 =
  case sub_mask x0 y0 of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x0 y0 =
  case x0 of {
   XI p -> add y0 (XO (mul p y0));
   XO p -> XO (mul p y0);
   XH -> y0}

iter :: Positive -> (a1 -> a1) -> a1 -> a1
iter n f x0 =
  case n of {
   XI n' -> f (iter n' f (iter n' f x0));
   XO n' -> iter n' f (iter n' f x0);
   XH -> f x0}

pow :: Positive -> Positive -> Positive
pow x0 y0 =
  iter y0 (mul x0) XH

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
compare_cont x0 y0 r =
  case x0 of {
   XI p ->
    case y0 of {
     XI q -> compare_cont p q r;
     XO q -> compare_cont p q Gt;
     XH -> Gt};
   XO p ->
    case y0 of {
     XI q -> compare_cont p q Lt;
     XO q -> compare_cont p q r;
     XH -> Gt};
   XH ->
    case y0 of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare x0 y0 =
  compare_cont x0 y0 Eq

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

eqb :: Positive -> Positive -> Prelude.Bool
eqb p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> eqb p0 q0;
     _ -> Prelude.False};
   XO p0 ->
    case q of {
     XO q0 -> eqb p0 q0;
     _ -> Prelude.False};
   XH ->
    case q of {
     XH -> Prelude.True;
     _ -> Prelude.False}}

leb :: Positive -> Positive -> Prelude.Bool
leb x0 y0 =
  case compare x0 y0 of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb :: Positive -> Positive -> Prelude.Bool
ltb x0 y0 =
  case compare x0 y0 of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

sqrtrem_step :: (Positive -> Positive) -> (Positive -> Positive) -> ((,)
                Positive Mask) -> (,) Positive Mask
sqrtrem_step f g p =
  case p of {
   (,) s y0 ->
    case y0 of {
     IsPos r ->
      let {s' = XI (XO s)} in
      let {r' = g (f r)} in
      case leb s' r' of {
       Prelude.True -> (,) (XI s) (sub_mask r' s');
       Prelude.False -> (,) (XO s) (IsPos r')};
     _ -> (,) (XO s) (sub_mask (g (f XH)) (XO (XO XH)))}}

sqrtrem :: Positive -> (,) Positive Mask
sqrtrem p =
  case p of {
   XI p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x0 -> XI x0) (\x0 -> XI x0) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x0 -> XO x0) (\x0 -> XI x0) (sqrtrem p1);
     XH -> (,) XH (IsPos (XO XH))};
   XO p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x0 -> XI x0) (\x0 -> XO x0) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x0 -> XO x0) (\x0 -> XO x0) (sqrtrem p1);
     XH -> (,) XH (IsPos XH)};
   XH -> (,) XH IsNul}

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

ggcdn :: Nat -> Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcdn n a b =
  case n of {
   O -> (,) XH ((,) a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> (,) a ((,) XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa (add aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,) (add bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) aa (XO bb))}};
       XH -> (,) XH ((,) a XH)};
     XO a0 ->
      case b of {
       XI p ->
        case ggcdn n0 a0 b of {
         (,) g p0 ->
          case p0 of {
           (,) aa bb -> (,) g ((,) (XO aa) bb)}};
       XO b0 ->
        case ggcdn n0 a0 b0 of {
         (,) g p -> (,) (XO g) p};
       XH -> (,) XH ((,) a XH)};
     XH -> (,) XH ((,) XH b)}}

ggcd :: Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcd a b =
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x0 =
  case x0 of {
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
  nat_iter n (\x0 -> XO x0) p

shiftr_nat :: Positive -> Nat -> Positive
shiftr_nat p n =
  nat_iter n div2 p

shiftl :: Positive -> N -> Positive
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 (\x0 -> XO x0) p}

shiftr :: Positive -> N -> Positive
shiftr p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 div2 p}

testbit_nat :: Positive -> Nat -> Prelude.Bool
testbit_nat p n =
  case p of {
   XI p0 ->
    case n of {
     O -> Prelude.True;
     S n' -> testbit_nat p0 n'};
   XO p0 ->
    case n of {
     O -> Prelude.False;
     S n' -> testbit_nat p0 n'};
   XH ->
    case n of {
     O -> Prelude.True;
     S n0 -> Prelude.False}}

testbit :: Positive -> N -> Prelude.Bool
testbit p n =
  case p of {
   XI p0 ->
    case n of {
     N0 -> Prelude.True;
     Npos n0 -> testbit p0 (pred_N n0)};
   XO p0 ->
    case n of {
     N0 -> Prelude.False;
     Npos n0 -> testbit p0 (pred_N n0)};
   XH ->
    case n of {
     N0 -> Prelude.True;
     Npos p0 -> Prelude.False}}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x0 =
  iter_op plus x0 (S O)

of_nat :: Nat -> Positive
of_nat n =
  case n of {
   O -> XH;
   S x0 ->
    case x0 of {
     O -> XH;
     S n0 -> succ (of_nat x0)}}

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x0 -> succ (of_succ_nat x0)}

eq_dec :: Positive -> Positive -> Prelude.Bool
eq_dec x0 y0 =
  positive_rec (\p h y1 ->
    case y1 of {
     XI p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (h p0);
     _ -> Prelude.False}) (\p h y1 ->
    case y1 of {
     XO p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (h p0);
     _ -> Prelude.False}) (\y1 ->
    case y1 of {
     XH -> Prelude.True;
     _ -> Prelude.False}) x0 y0

peano_rect :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rect a f p =
  let {f2 = peano_rect (f XH a) (\p0 x0 -> f (succ (XO p0)) (f (XO p0) x0))}
  in
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

leb_spec0 :: Positive -> Positive -> Reflect
leb_spec0 x0 y0 =
  iff_reflect (leb x0 y0)

ltb_spec0 :: Positive -> Positive -> Reflect
ltb_spec0 x0 y0 =
  iff_reflect (ltb x0 y0)

max_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max n m) __ (hl __);
   _ -> compat m (max n m) __ (hr __)}

max_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
max_case n m x0 x1 x2 =
  max_case_strong n m x0 (\_ -> x1) (\_ -> x2)

max_dec :: Positive -> Positive -> Prelude.Bool
max_dec n m =
  max_case n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

min_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min n m) __ (hr __);
   _ -> compat n (min n m) __ (hl __)}

min_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
min_case n m x0 x1 x2 =
  min_case_strong n m x0 (\_ -> x1) (\_ -> x2)

min_dec :: Positive -> Positive -> Prelude.Bool
min_dec n m =
  min_case n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

max_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
max_case_strong0 n m x0 x1 =
  max_case_strong n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

max_case0 :: Positive -> Positive -> a1 -> a1 -> a1
max_case0 n m x0 x1 =
  max_case_strong0 n m (\_ -> x0) (\_ -> x1)

max_dec0 :: Positive -> Positive -> Prelude.Bool
max_dec0 =
  max_dec

min_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
min_case_strong0 n m x0 x1 =
  min_case_strong n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

min_case0 :: Positive -> Positive -> a1 -> a1 -> a1
min_case0 n m x0 x1 =
  min_case_strong0 n m (\_ -> x0) (\_ -> x1)

min_dec0 :: Positive -> Positive -> Prelude.Bool
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
succ_double x0 =
  case x0 of {
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
    case p0 of {
     XI p -> Npos p;
     XO p -> Npos p;
     XH -> N0}}

even :: N -> Prelude.Bool
even n =
  case n of {
   N0 -> Prelude.True;
   Npos p ->
    case p of {
     XO p0 -> Prelude.True;
     _ -> Prelude.False}}

odd :: N -> Prelude.Bool
odd n =
  Prelude.not (even n)

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

pos_div_eucl :: Positive -> N -> (,) N N
pos_div_eucl a b =
  case a of {
   XI a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}};
   XO a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}};
   XH ->
    case b of {
     N0 -> (,) N0 (Npos XH);
     Npos p ->
      case p of {
       XH -> (,) (Npos XH) N0;
       _ -> (,) N0 (Npos XH)}}}

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
   N0 -> (,) b ((,) N0 (Npos XH));
   Npos p ->
    case b of {
     N0 -> (,) a ((,) (Npos XH) N0);
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

discr :: N -> Prelude.Maybe Positive
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
  case compare0 (Npos XH) a of {
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
   Prelude.True -> Npos XH;
   Prelude.False -> N0}

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
double0 x0 =
  case x0 of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double0 :: Z -> Z
succ_double0 x0 =
  case x0 of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x0 =
  case x0 of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x0 y0 =
  case x0 of {
   XI p ->
    case y0 of {
     XI q -> double0 (pos_sub p q);
     XO q -> succ_double0 (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y0 of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double0 (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y0 of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add1 :: Z -> Z -> Z
add1 x0 y0 =
  case x0 of {
   Z0 -> y0;
   Zpos x' ->
    case y0 of {
     Z0 -> x0;
     Zpos y' -> Zpos (add x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y0 of {
     Z0 -> x0;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add x' y')}}

opp :: Z -> Z
opp x0 =
  case x0 of {
   Z0 -> Z0;
   Zpos x1 -> Zneg x1;
   Zneg x1 -> Zpos x1}

succ1 :: Z -> Z
succ1 x0 =
  add1 x0 (Zpos XH)

pred1 :: Z -> Z
pred1 x0 =
  add1 x0 (Zneg XH)

sub1 :: Z -> Z -> Z
sub1 m n =
  add1 m (opp n)

mul1 :: Z -> Z -> Z
mul1 x0 y0 =
  case x0 of {
   Z0 -> Z0;
   Zpos x' ->
    case y0 of {
     Z0 -> Z0;
     Zpos y' -> Zpos (mul x' y');
     Zneg y' -> Zneg (mul x' y')};
   Zneg x' ->
    case y0 of {
     Z0 -> Z0;
     Zpos y' -> Zneg (mul x' y');
     Zneg y' -> Zpos (mul x' y')}}

pow_pos :: Z -> Positive -> Z
pow_pos z n =
  iter n (mul1 z) (Zpos XH)

pow1 :: Z -> Z -> Z
pow1 x0 y0 =
  case y0 of {
   Z0 -> Zpos XH;
   Zpos p -> pow_pos x0 p;
   Zneg p -> Z0}

square1 :: Z -> Z
square1 x0 =
  case x0 of {
   Z0 -> Z0;
   Zpos p -> Zpos (square p);
   Zneg p -> Zpos (square p)}

compare1 :: Z -> Z -> Comparison
compare1 x0 y0 =
  case x0 of {
   Z0 ->
    case y0 of {
     Z0 -> Eq;
     Zpos y' -> Lt;
     Zneg y' -> Gt};
   Zpos x' ->
    case y0 of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y0 of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

sgn :: Z -> Z
sgn z =
  case z of {
   Z0 -> Z0;
   Zpos p -> Zpos XH;
   Zneg p -> Zneg XH}

leb1 :: Z -> Z -> Prelude.Bool
leb1 x0 y0 =
  case compare1 x0 y0 of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb1 :: Z -> Z -> Prelude.Bool
ltb1 x0 y0 =
  case compare1 x0 y0 of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

geb :: Z -> Z -> Prelude.Bool
geb x0 y0 =
  case compare1 x0 y0 of {
   Lt -> Prelude.False;
   _ -> Prelude.True}

gtb :: Z -> Z -> Prelude.Bool
gtb x0 y0 =
  case compare1 x0 y0 of {
   Gt -> Prelude.True;
   _ -> Prelude.False}

eqb1 :: Z -> Z -> Prelude.Bool
eqb1 x0 y0 =
  case x0 of {
   Z0 ->
    case y0 of {
     Z0 -> Prelude.True;
     _ -> Prelude.False};
   Zpos p ->
    case y0 of {
     Zpos q -> eqb p q;
     _ -> Prelude.False};
   Zneg p ->
    case y0 of {
     Zneg q -> eqb p q;
     _ -> Prelude.False}}

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
   x0 -> x0}

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
iter1 n f x0 =
  case n of {
   Zpos p -> iter p f x0;
   _ -> x0}

pos_div_eucl0 :: Positive -> Z -> (,) Z Z
pos_div_eucl0 a b =
  case a of {
   XI a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {r' = add1 (mul1 (Zpos (XO XH)) r) (Zpos XH)} in
      case ltb1 r' b of {
       Prelude.True -> (,) (mul1 (Zpos (XO XH)) q) r';
       Prelude.False -> (,) (add1 (mul1 (Zpos (XO XH)) q) (Zpos XH))
        (sub1 r' b)}};
   XO a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {r' = mul1 (Zpos (XO XH)) r} in
      case ltb1 r' b of {
       Prelude.True -> (,) (mul1 (Zpos (XO XH)) q) r';
       Prelude.False -> (,) (add1 (mul1 (Zpos (XO XH)) q) (Zpos XH))
        (sub1 r' b)}};
   XH ->
    case leb1 (Zpos (XO XH)) b of {
     Prelude.True -> (,) Z0 (Zpos XH);
     Prelude.False -> (,) (Zpos XH) Z0}}

div_eucl0 :: Z -> Z -> (,) Z Z
div_eucl0 a b =
  case a of {
   Z0 -> (,) Z0 Z0;
   Zpos a' ->
    case b of {
     Z0 -> (,) Z0 Z0;
     Zpos p -> pos_div_eucl0 a' b;
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       (,) q r ->
        case r of {
         Z0 -> (,) (opp q) Z0;
         _ -> (,) (opp (add1 q (Zpos XH))) (add1 b r)}}};
   Zneg a' ->
    case b of {
     Z0 -> (,) Z0 Z0;
     Zpos p ->
      case pos_div_eucl0 a' b of {
       (,) q r ->
        case r of {
         Z0 -> (,) (opp q) Z0;
         _ -> (,) (opp (add1 q (Zpos XH))) (sub1 b r)}};
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       (,) q r -> (,) q (opp r)}}}

div1 :: Z -> Z -> Z
div1 a b =
  case div_eucl0 a b of {
   (,) q x0 -> q}

modulo0 :: Z -> Z -> Z
modulo0 a b =
  case div_eucl0 a b of {
   (,) x0 r -> r}

quotrem :: Z -> Z -> (,) Z Z
quotrem a b =
  case a of {
   Z0 -> (,) Z0 Z0;
   Zpos a0 ->
    case b of {
     Z0 -> (,) Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (of_N q) (of_N r)};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (opp (of_N q)) (of_N r)}};
   Zneg a0 ->
    case b of {
     Z0 -> (,) Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (opp (of_N q)) (opp (of_N r))};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (of_N q) (opp (of_N r))}}}

quot :: Z -> Z -> Z
quot a b =
  fst (quotrem a b)

rem :: Z -> Z -> Z
rem a b =
  snd (quotrem a b)

even0 :: Z -> Prelude.Bool
even0 z =
  case z of {
   Z0 -> Prelude.True;
   Zpos p ->
    case p of {
     XO p0 -> Prelude.True;
     _ -> Prelude.False};
   Zneg p ->
    case p of {
     XO p0 -> Prelude.True;
     _ -> Prelude.False}}

odd0 :: Z -> Prelude.Bool
odd0 z =
  case z of {
   Z0 -> Prelude.False;
   Zpos p ->
    case p of {
     XO p0 -> Prelude.False;
     _ -> Prelude.True};
   Zneg p ->
    case p of {
     XO p0 -> Prelude.False;
     _ -> Prelude.True}}

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

sqrtrem1 :: Z -> (,) Z Z
sqrtrem1 n =
  case n of {
   Zpos p ->
    case sqrtrem p of {
     (,) s m ->
      case m of {
       IsPos r -> (,) (Zpos s) (Zpos r);
       _ -> (,) (Zpos s) Z0}};
   _ -> (,) Z0 Z0}

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

ggcd1 :: Z -> Z -> (,) Z ((,) Z Z)
ggcd1 a b =
  case a of {
   Z0 -> (,) (abs b) ((,) Z0 (sgn b));
   Zpos a0 ->
    case b of {
     Z0 -> (,) (abs a) ((,) (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zpos aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zpos aa) (Zneg bb))}}};
   Zneg a0 ->
    case b of {
     Z0 -> (,) (abs a) ((,) (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zneg aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zneg aa) (Zneg bb))}}}}

testbit1 :: Z -> Z -> Prelude.Bool
testbit1 a n =
  case n of {
   Z0 -> odd0 a;
   Zpos p ->
    case a of {
     Z0 -> Prelude.False;
     Zpos a0 -> testbit a0 (Npos p);
     Zneg a0 -> Prelude.not (testbit0 (pred_N a0) (Npos p))};
   Zneg p -> Prelude.False}

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

eq_dec1 :: Z -> Z -> Prelude.Bool
eq_dec1 x0 y0 =
  z_rec (\y1 ->
    case y1 of {
     Z0 -> Prelude.True;
     _ -> Prelude.False}) (\p y1 ->
    case y1 of {
     Zpos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0);
     _ -> Prelude.False}) (\p y1 ->
    case y1 of {
     Zneg p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0);
     _ -> Prelude.False}) x0 y0

leb_spec2 :: Z -> Z -> Reflect
leb_spec2 x0 y0 =
  iff_reflect (leb1 x0 y0)

ltb_spec2 :: Z -> Z -> Reflect
ltb_spec2 x0 y0 =
  iff_reflect (ltb1 x0 y0)

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
eqb_spec1 x0 y0 =
  iff_reflect (eqb1 x0 y0)

b2z :: Prelude.Bool -> Z
b2z b =
  case b of {
   Prelude.True -> Zpos XH;
   Prelude.False -> Z0}

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
max_case3 n m x0 x1 x2 =
  max_case_strong3 n m x0 (\_ -> x1) (\_ -> x2)

max_dec3 :: Z -> Z -> Prelude.Bool
max_dec3 n m =
  max_case3 n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

min_case_strong3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat m (min1 n m) __ (hr __);
   _ -> compat n (min1 n m) __ (hl __)}

min_case3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case3 n m x0 x1 x2 =
  min_case_strong3 n m x0 (\_ -> x1) (\_ -> x2)

min_dec3 :: Z -> Z -> Prelude.Bool
min_dec3 n m =
  min_case3 n m (\x0 y0 _ h0 -> h0) Prelude.True Prelude.False

max_case_strong4 :: Z -> Z -> (() -> a1) -> (() -> a1) -> a1
max_case_strong4 n m x0 x1 =
  max_case_strong3 n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

max_case4 :: Z -> Z -> a1 -> a1 -> a1
max_case4 n m x0 x1 =
  max_case_strong4 n m (\_ -> x0) (\_ -> x1)

max_dec4 :: Z -> Z -> Prelude.Bool
max_dec4 =
  max_dec3

min_case_strong4 :: Z -> Z -> (() -> a1) -> (() -> a1) -> a1
min_case_strong4 n m x0 x1 =
  min_case_strong3 n m (\x2 y0 _ x3 -> eq_rect __ x3 __) x0 x1

min_case4 :: Z -> Z -> a1 -> a1 -> a1
min_case4 n m x0 x1 =
  min_case_strong4 n m (\_ -> x0) (\_ -> x1)

min_dec4 :: Z -> Z -> Prelude.Bool
min_dec4 =
  min_dec3

z_lt_dec :: Z -> Z -> Prelude.Bool
z_lt_dec x0 y0 =
  case compare1 x0 y0 of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

z_lt_ge_dec :: Z -> Z -> Prelude.Bool
z_lt_ge_dec x0 y0 =
  z_lt_dec x0 y0

z_lt_le_dec :: Z -> Z -> Prelude.Bool
z_lt_le_dec x0 y0 =
  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (z_lt_ge_dec x0 y0)

pow_pos0 :: (a1 -> a1 -> a1) -> a1 -> Positive -> a1
pow_pos0 rmul x0 i =
  case i of {
   XI i0 -> let {p = pow_pos0 rmul x0 i0} in rmul x0 (rmul p p);
   XO i0 -> let {p = pow_pos0 rmul x0 i0} in rmul p p;
   XH -> x0}

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
inject_Z x0 =
  Qmake x0 XH

qcompare :: Q -> Q -> Comparison
qcompare p q =
  compare1 (mul1 (qnum p) (Zpos (qden q))) (mul1 (qnum q) (Zpos (qden p)))

qeq_dec :: Q -> Q -> Prelude.Bool
qeq_dec x0 y0 =
  eq_dec1 (mul1 (qnum x0) (Zpos (qden y0))) (mul1 (qnum y0) (Zpos (qden x0)))

qplus :: Q -> Q -> Q
qplus x0 y0 =
  Qmake
    (add1 (mul1 (qnum x0) (Zpos (qden y0)))
      (mul1 (qnum y0) (Zpos (qden x0)))) (mul (qden x0) (qden y0))

qmult :: Q -> Q -> Q
qmult x0 y0 =
  Qmake (mul1 (qnum x0) (qnum y0)) (mul (qden x0) (qden y0))

qopp :: Q -> Q
qopp x0 =
  Qmake (opp (qnum x0)) (qden x0)

qminus :: Q -> Q -> Q
qminus x0 y0 =
  qplus x0 (qopp y0)

qinv :: Q -> Q
qinv x0 =
  case qnum x0 of {
   Z0 -> Qmake Z0 XH;
   Zpos p -> Qmake (Zpos (qden x0)) p;
   Zneg p -> Qmake (Zneg (qden x0)) p}

qdiv :: Q -> Q -> Q
qdiv x0 y0 =
  qmult x0 (qinv y0)

qlt_le_dec :: Q -> Q -> Prelude.Bool
qlt_le_dec x0 y0 =
  z_lt_le_dec (mul1 (qnum x0) (Zpos (qden y0)))
    (mul1 (qnum y0) (Zpos (qden x0)))

qpower_positive :: Q -> Positive -> Q
qpower_positive q p =
  pow_pos0 qmult q p

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
     (,) r1 r2 -> Qmake r1 (to_pos r2)}}

qminus' :: Q -> Q -> Q
qminus' x0 y0 =
  qred (qminus x0 y0)

qabs :: Q -> Q
qabs x0 =
  case x0 of {
   Qmake n d -> Qmake (abs n) d}

qfloor :: Q -> Z
qfloor x0 =
  case x0 of {
   Qmake n d -> div1 n (Zpos d)}

ap_Q_cotransitive0 :: Q -> Q -> Q -> Prelude.Either () ()
ap_Q_cotransitive0 x0 y0 z =
  case qeq_dec x0 z of {
   Prelude.True -> Prelude.Right __;
   Prelude.False -> Prelude.Left __}

qplus_strext0 :: Q -> Q -> Q -> Q -> Prelude.Either () ()
qplus_strext0 x1 x2 y1 y2 =
  case qeq_dec x1 x2 of {
   Prelude.True -> Prelude.Right __;
   Prelude.False -> Prelude.Left __}

ap_Q_cotransitive1 :: Q -> Q -> Q -> Prelude.Either () ()
ap_Q_cotransitive1 x0 y0 z =
  ap_Q_cotransitive0 x0 y0 z

ap_Q_is_apartness :: Is_CSetoid Q ()
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

qpos_one :: Qpos
qpos_one =
  Qmake (Zpos XH) XH

qpos_mult :: Qpos -> Qpos -> Qpos
qpos_mult x0 y0 =
  qmult (qposAsQ x0) (qposAsQ y0)

qpos_inv :: Qpos -> Qpos
qpos_inv x0 =
  qinv (qposAsQ x0)

qabsQpos :: Q -> Qpos
qabsQpos x0 =
  case x0 of {
   Qmake qnum0 ad ->
    case qnum0 of {
     Z0 -> qpos_one;
     Zpos an -> qposMake an ad;
     Zneg an -> qposMake an ad}}

data RosTopicType rT =
   Build_RosTopicType

type TopicType rT = Any

type Header =
  Q
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

mkDelayedMesg :: (DecEq a1) -> (RosTopicType a1) -> a1 -> Q -> (TopicType 
                 a1) -> Message a1
mkDelayedMesg deq h outTopic delay payload =
  (,) (ExistT outTopic payload) delay

type PureProcWDelay rosTopic =
  (TopicType rosTopic) -> ([]) ((,) Q (TopicType rosTopic))

delayedLift2Mesg :: (DecEq a1) -> (RosTopicType a1) -> a1 -> a1 ->
                    (PureProcWDelay a1) -> (Message a1) -> ([]) (Message a1)
delayedLift2Mesg deq h inTopic outTopic f inpMesg =
  case getPayload deq h inTopic inpMesg of {
   Prelude.Just tmesg ->
    map (\p -> mkDelayedMesg deq h outTopic (fst p) (snd p)) (f tmesg);
   Prelude.Nothing -> ([])}

min2 :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> a1
min2 le_total x0 y0 =
  case le_total x0 y0 of {
   Prelude.True -> x0;
   Prelude.False -> y0}

min_case5 :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> (() -> a2) -> (() ->
             a2) -> a2
min_case5 le_total x0 y0 hx hy =
  case le_total x0 y0 of {
   Prelude.True -> hx __;
   Prelude.False -> hy __}

max2 :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> a1
max2 le_total x0 y0 =
  case le_total y0 x0 of {
   Prelude.True -> x0;
   Prelude.False -> y0}

max_case5 :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> (() -> a2) -> (() ->
             a2) -> a2
max_case5 le_total x0 y0 x1 x2 =
  let {flip_le_total = \x3 y1 -> le_total y1 x3} in
  min_case5 flip_le_total x0 y0 x1 x2

qlt_le_dec_fast :: Q -> Q -> Prelude.Bool
qlt_le_dec_fast x0 y0 =
  let {c = qcompare x0 y0} in
  case c of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

qle_total :: Q -> Q -> Prelude.Bool
qle_total x0 y0 =
  qlt_le_dec_fast x0 y0

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
              (qposInf_mult (Qpos2QposInf (qposMake XH (XO XH))) e)))) x1))
    (qposInf_mult (Qpos2QposInf (qposMake XH (XO XH))) e)

cap_fun :: MetricSpace -> MetricSpace -> St_car -> St_car -> St_car
cap_fun x0 y0 f x1 =
  unsafeCoerce (cap_raw x0 y0 f x1)

cap_modulus :: MetricSpace -> MetricSpace -> St_car -> Qpos -> QposInf
cap_modulus x0 y0 f e =
  mu x0 y0
    (unsafeCoerce
      (approximate (uniformlyContinuousSpace x0 y0) (unsafeCoerce f)
        (Qpos2QposInf (qpos_mult (qposMake XH (XI XH)) e))))
    (qpos_mult (qposMake XH (XI XH)) e)

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

q_0 :: Zero Q
q_0 =
  Qmake Z0 XH

q_1 :: One Q
q_1 =
  Qmake (Zpos XH) XH

q_opp :: Negate Q
q_opp =
  qopp

q_plus :: Plus Q
q_plus =
  qplus

q_mult :: Mult Q
q_mult =
  qmult

decision_instance_0 :: Q -> Q -> Decision
decision_instance_0 =
  qeq_dec

inject_Z_Q :: Cast Z Q
inject_Z_Q =
  inject_Z

decision_instance_1 :: Q -> Q -> Decision
decision_instance_1 y0 x0 =
  let {filtered_var = qlt_le_dec x0 y0} in
  case filtered_var of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

cR :: MetricSpace
cR =
  complete q_as_MetricSpace

inject_Q_CR :: Cast Q St_car
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

qscale_modulus :: Q -> Qpos -> QposInf
qscale_modulus a e =
  case a of {
   Qmake qnum0 ad ->
    case qnum0 of {
     Z0 -> QposInfinity;
     Zpos an -> Qpos2QposInf (qpos_mult (qposMake ad an) e);
     Zneg an -> Qpos2QposInf (qpos_mult (qposMake ad an) e)}}

qscale_uc :: St_car -> St_car
qscale_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce (qmult (unsafeCoerce a) (unsafeCoerce b)))
    (qscale_modulus (unsafeCoerce a)))

scale :: Q -> St_car
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
  ucFun2 cR cR cR (cRmult_bounded (cR_b (qposMake XH XH) y0)) x0 y0

approximateQ :: Q -> Positive -> Q
approximateQ x0 p =
  case x0 of {
   Qmake n d -> Qmake (div1 (mul1 n (Zpos p)) (Zpos d)) p}

root_step :: Q -> Q -> Q
root_step a b =
  qplus (qdiv b (Qmake (Zpos (XO XH)) XH))
    (qdiv a (qmult (Qmake (Zpos (XO XH)) XH) b))

initial_root :: Q -> Q
initial_root a =
  qmult (Qmake (Zpos XH) (XO XH)) (qplus a (Qmake (Zpos XH) XH))

root_loop :: Q -> Qpos -> Nat -> Q -> Positive -> Q
root_loop a e n b err =
  case n of {
   O -> b;
   S n' ->
    case qlt_le_dec_fast (qposAsQ e) (Qmake (Zpos XH) err) of {
     Prelude.True ->
      let {err' = mul err err} in
      root_loop a e n' (approximateQ (root_step a b) (mul (XO XH) err')) err';
     Prelude.False -> b}}

sqrt_raw :: Q -> QposInf -> Q
sqrt_raw a e =
  case e of {
   Qpos2QposInf e' ->
    root_loop a e' (S (size_nat (qden (qposAsQ e')))) (initial_root a) (XO
      XH);
   QposInfinity -> Qmake (Zpos XH) XH}

rational_sqrt_mid :: Q -> St_car
rational_sqrt_mid a =
  unsafeCoerce (unsafeCoerce (sqrt_raw a))

rational_sqrt_big_bounded :: Nat -> Q -> St_car
rational_sqrt_big_bounded n a =
  case n of {
   O -> inject_Q_CR (Qmake (Zpos XH) XH);
   S n0 ->
    let {s = qle_total a (Qmake (Zpos (XO (XO XH))) XH)} in
    case s of {
     Prelude.True -> rational_sqrt_mid a;
     Prelude.False ->
      ucFun cR cR (unsafeCoerce (scale (Qmake (Zpos (XO XH)) XH)))
        (rational_sqrt_big_bounded n0
          (qdiv a (Qmake (Zpos (XO (XO XH))) XH)))}}

rational_sqrt_small_bounded :: Nat -> Q -> St_car
rational_sqrt_small_bounded n a =
  case n of {
   O -> rational_sqrt_mid a;
   S n0 ->
    let {s = qle_total a (Qmake (Zpos XH) XH)} in
    case s of {
     Prelude.True ->
      ucFun cR cR (unsafeCoerce (scale (Qmake (Zpos XH) (XO XH))))
        (rational_sqrt_small_bounded n0
          (qmult (Qmake (Zpos (XO (XO XH))) XH) a));
     Prelude.False -> rational_sqrt_mid a}}

rational_sqrt_pos :: Q -> St_car
rational_sqrt_pos a =
  let {s = qle_total (Qmake (Zpos XH) XH) a} in
  case s of {
   Prelude.True ->
    rational_sqrt_big_bounded
      (case a of {
        Qmake n x0 ->
         case n of {
          Zpos p -> size_nat p;
          _ -> O}}) a;
   Prelude.False ->
    rational_sqrt_small_bounded
      (case a of {
        Qmake x0 d -> size_nat d}) a}

rational_sqrt :: Q -> St_car
rational_sqrt a =
  case qlt_le_dec_fast (Qmake Z0 XH) a of {
   Prelude.True -> rational_sqrt_pos a;
   Prelude.False -> inject_Q_CR (Qmake Z0 XH)}

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

partialAlternatingSumUntil :: ((Stream Q) -> Prelude.Bool) -> (Stream Q) -> Q
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

ppositives_help :: Positive -> Stream Positive
ppositives_help n =
  Cons n (ppositives_help (succ n))

ppositives :: Stream Positive
ppositives =
  ppositives_help XH

qrecip_positives :: Stream Q
qrecip_positives =
  map0 (\x0 -> Qmake (Zpos XH) x0) ppositives

arctanSequence :: Q -> Stream Q
arctanSequence a =
  mult_Streams q_mult (everyOther qrecip_positives)
    (powers_help q_mult (qpower a (Zpos (XO XH))) a)

rational_arctan_small_pos :: Q -> St_car
rational_arctan_small_pos a =
  infiniteAlternatingSum (arctanSequence a)

rational_arctan_small :: Q -> St_car
rational_arctan_small a =
  let {s = qle_total a (Qmake Z0 XH)} in
  case s of {
   Prelude.True -> cRopp (rational_arctan_small_pos (qopp a));
   Prelude.False -> rational_arctan_small_pos a}

r_pi :: Q -> St_car
r_pi r =
  ucFun2 cR cR cR cRplus_uc
    (ucFun2 cR cR cR cRplus_uc
      (ucFun cR cR
        (unsafeCoerce
          (scale
            (qmult (inject_Z (Zpos (XO (XO (XO (XO (XI (XI (XO XH))))))))) r)))
        (rational_arctan_small_pos (Qmake (Zpos XH) (XI (XO (XO (XI (XI
          XH))))))))
      (ucFun cR cR
        (unsafeCoerce
          (scale (qmult (inject_Z (Zpos (XO (XO (XI (XI XH)))))) r)))
        (rational_arctan_small_pos (Qmake (Zpos XH) (XI (XI (XI (XI (XO (XI
          (XI XH)))))))))))
    (ucFun2 cR cR cR cRplus_uc
      (ucFun cR cR
        (unsafeCoerce
          (scale
            (qmult (qopp (inject_Z (Zpos (XO (XO (XO (XO (XI XH)))))))) r)))
        (rational_arctan_small_pos (Qmake (Zpos XH) (XO (XI (XO (XI (XO (XI
          (XO (XI (XO XH))))))))))))
      (ucFun cR cR
        (unsafeCoerce
          (scale
            (qmult (inject_Z (Zpos (XO (XO (XO (XO (XO (XI XH)))))))) r)))
        (rational_arctan_small_pos (Qmake (Zpos XH) (XI (XI (XI (XI (XO (XO
          (XO (XI (XO (XI (XO (XO (XI XH)))))))))))))))))

cRpi :: St_car
cRpi =
  r_pi (Qmake (Zpos XH) XH)

rational_arctan_big_pos :: Q -> St_car
rational_arctan_big_pos a =
  ucFun2 cR cR cR cRplus_uc (r_pi (Qmake (Zpos XH) (XO XH)))
    (cRopp (rational_arctan_small_pos (qinv a)))

rational_arctan_mid_pos :: Q -> St_car
rational_arctan_mid_pos a =
  ucFun2 cR cR cR cRplus_uc (r_pi (Qmake (Zpos XH) (XO (XO XH))))
    (rational_arctan_small
      (qdiv (qminus a (Qmake (Zpos XH) XH)) (qplus a (Qmake (Zpos XH) XH))))

rational_arctan_pos :: Q -> St_car
rational_arctan_pos a =
  let {s = qle_total (Qmake (Zpos (XO XH)) (XI (XO XH))) a} in
  case s of {
   Prelude.True ->
    let {s0 = qle_total (Qmake (Zpos (XI (XO XH))) (XO XH)) a} in
    case s0 of {
     Prelude.True -> rational_arctan_big_pos a;
     Prelude.False -> rational_arctan_mid_pos a};
   Prelude.False -> rational_arctan_small_pos a}

rational_arctan :: Q -> St_car
rational_arctan a =
  let {s = qle_total a (Qmake Z0 XH)} in
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

rational_sqrt_SqrtFun_instance :: SqrtFun Q St_car
rational_sqrt_SqrtFun_instance =
  rational_sqrt

normSpace_instance_0 :: NormSpace St_car St_car
normSpace_instance_0 =
  ucFun cR cR (unsafeCoerce cRabs)

cRpi_RealNumberPi_instance :: RealNumberPi St_car
cRpi_RealNumberPi_instance =
  cRpi

q_Half_instance :: HalfNum Q
q_Half_instance =
  Qmake (Zpos XH) (XO XH)

qSign :: (Negate a1) -> Q -> a1 -> a1
qSign h q a =
  case decide (lt_dec decision_instance_1 q (zero1 q_0)) of {
   Prelude.True -> negate h a;
   Prelude.False -> a}

q2Zapprox :: Q -> Z
q2Zapprox q =
  let {qf = qfloor q} in
  case decide
         (decision_instance_1 (qminus q (inject_Z qf)) (Qmake (Zpos XH) (XO
           XH))) of {
   Prelude.True -> qf;
   Prelude.False -> add1 qf (Zpos XH)}

r2ZApprox :: St_car -> Qpos -> Z
r2ZApprox r eps =
  q2Zapprox
    (unsafeCoerce
      (approximate q_as_MetricSpace (unsafeCoerce r) (Qpos2QposInf eps)))

cast_instance_0 :: Cast Positive St_car
cast_instance_0 =
  compose (compose (cast inject_Q_CR) (cast inject_Z_Q)) (\x0 -> Zpos x0)

simpleApproximate :: St_car -> Positive -> Qpos -> Q
simpleApproximate r den eps =
  Qmake (r2ZApprox (mult cRmult r (cast cast_instance_0 den)) eps) den

qSignHalf :: Q -> Q
qSignHalf q =
  qSign q_opp q (half_num q_Half_instance)

polarTheta :: (Cart2D Q) -> St_car
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

polar__U03b8_Sign :: (Cart2D Q) -> Q
polar__U03b8_Sign target =
  qSign q_opp (y target) (one1 q_1)

cart2Polar :: (Cart2D Q) -> Polar2D St_car
cart2Polar cart =
  MkPolar2D
    (norm
      (normSpace_instance_Cart2D rational_sqrt_SqrtFun_instance q_plus
        q_mult) cart) (polarTheta cart)

robotPureProgam :: Qpos -> Qpos -> Qpos -> Qpos -> Positive -> (Cart2D 
                   Q) -> ([]) ((,) Q (Polar2D Q))
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
  (zero1 q_0))) ((:) ((,) (cast (nonNeg_inject (Qmake Z0 XH)) delay)
  (MkPolar2D (cast (nonNeg_inject (Qmake Z0 XH)) speed) (zero1 q_0))) ((:)
  ((,) (simpleApproximate translDuration delRes delEps) (MkPolar2D
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
  qposMake XH (XO XH)

speedMetresPerSec :: Qpos
speedMetresPerSec =
  qposMake XH (XO (XI (XO XH)))

delResSecInv :: Positive
delResSecInv =
  XO (XO (XO (XI (XO (XI (XI (XI (XI XH))))))))

delEpsSec :: Qpos
delEpsSec =
  qposMake XH (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO
    XH)))))))))))))

initDelayLin :: Qpos
initDelayLin =
  qposMake XH XH

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

target1Metres :: Cart2D Q
target1Metres =
  MkCart2D (Qmake (Zpos XH) XH) (Qmake (Zpos XH) XH)

robotOutput :: ([]) ((,) Q (Polar2D Q))
robotOutput =
  unsafeCoerce
    (robotProgramInstance initDelayLin (unsafeCoerce target1Metres))

projNums :: ((,) Q (Polar2D Q)) -> (,) ((,) Z Z) Z
projNums inp =
  case inp of {
   (,) del pos -> (,) ((,) (qnum del) (qnum (rad pos))) (qnum (__U03b8_ pos))}

robotOutputInts :: ([]) ((,) ((,) Z Z) Z)
robotOutputInts =
  map projNums robotOutput

map3 :: (a1 -> a2) -> ((,) ((,) a1 a1) a1) -> (,) ((,) a2 a2) a2
map3 f inp =
  case inp of {
   (,) xy z ->
    case xy of {
     (,) x0 y0 -> (,) ((,) (f x0) (f y0)) (f z)}}

