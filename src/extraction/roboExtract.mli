type __ = Obj.t

type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

val plus : nat -> nat -> nat

val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod
    -> (positive, mask) prod
  
  val sqrtrem : positive -> (positive, mask) prod
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod
  
  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
 end

module Coq_Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod
    -> (positive, mask) prod
  
  val sqrtrem : positive -> (positive, mask) prod
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod
  
  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
  
  val eq_dec : positive -> positive -> sumbool
  
  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  val coq_PeanoView_rect :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val coq_PeanoView_rec :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView : positive -> coq_PeanoView
  
  val coq_PeanoView_iter :
    'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1
  
  val eqb_spec : positive -> positive -> reflect
  
  val switch_Eq : comparison -> comparison -> comparison
  
  val mask2cmp : mask -> comparison
  
  val leb_spec0 : positive -> positive -> reflect
  
  val ltb_spec0 : positive -> positive -> reflect
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      'a1 -> 'a1 -> 'a1
    
    val max_dec : positive -> positive -> sumbool
    
    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      'a1 -> 'a1 -> 'a1
    
    val min_dec : positive -> positive -> sumbool
   end
  
  val max_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : positive -> positive -> sumbool
  
  val min_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : positive -> positive -> sumbool
 end

module N : 
 sig 
  type t = n
  
  val zero : n
  
  val one : n
  
  val two : n
  
  val succ_double : n -> n
  
  val double : n -> n
  
  val succ : n -> n
  
  val pred : n -> n
  
  val succ_pos : n -> positive
  
  val add : n -> n -> n
  
  val sub : n -> n -> n
  
  val mul : n -> n -> n
  
  val compare : n -> n -> comparison
  
  val eqb : n -> n -> bool
  
  val leb : n -> n -> bool
  
  val ltb : n -> n -> bool
  
  val min : n -> n -> n
  
  val max : n -> n -> n
  
  val div2 : n -> n
  
  val even : n -> bool
  
  val odd : n -> bool
  
  val pow : n -> n -> n
  
  val square : n -> n
  
  val log2 : n -> n
  
  val size : n -> n
  
  val size_nat : n -> nat
  
  val pos_div_eucl : positive -> n -> (n, n) prod
  
  val div_eucl : n -> n -> (n, n) prod
  
  val div : n -> n -> n
  
  val modulo : n -> n -> n
  
  val gcd : n -> n -> n
  
  val ggcd : n -> n -> (n, (n, n) prod) prod
  
  val sqrtrem : n -> (n, n) prod
  
  val sqrt : n -> n
  
  val coq_lor : n -> n -> n
  
  val coq_land : n -> n -> n
  
  val ldiff : n -> n -> n
  
  val coq_lxor : n -> n -> n
  
  val shiftl_nat : n -> nat -> n
  
  val shiftr_nat : n -> nat -> n
  
  val shiftl : n -> n -> n
  
  val shiftr : n -> n -> n
  
  val testbit_nat : n -> nat -> bool
  
  val testbit : n -> n -> bool
  
  val to_nat : n -> nat
  
  val of_nat : nat -> n
  
  val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val eq_dec : n -> n -> sumbool
  
  val discr : n -> positive sumor
  
  val binary_rect : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val binary_rec : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val leb_spec0 : n -> n -> reflect
  
  val ltb_spec0 : n -> n -> reflect
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  module Private_NZPow : 
   sig 
    
   end
  
  module Private_NZSqrt : 
   sig 
    
   end
  
  val sqrt_up : n -> n
  
  val log2_up : n -> n
  
  module Private_NZDiv : 
   sig 
    
   end
  
  val lcm : n -> n -> n
  
  val eqb_spec : n -> n -> reflect
  
  val b2n : bool -> n
  
  val setbit : n -> n -> n
  
  val clearbit : n -> n -> n
  
  val ones : n -> n
  
  val lnot : n -> n -> n
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : n -> n -> sumbool
    
    val min_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : n -> n -> sumbool
   end
  
  val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : n -> n -> sumbool
  
  val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : n -> n -> sumbool
 end

module Z : 
 sig 
  type t = z
  
  val zero : z
  
  val one : z
  
  val two : z
  
  val double : z -> z
  
  val succ_double : z -> z
  
  val pred_double : z -> z
  
  val pos_sub : positive -> positive -> z
  
  val add : z -> z -> z
  
  val opp : z -> z
  
  val succ : z -> z
  
  val pred : z -> z
  
  val sub : z -> z -> z
  
  val mul : z -> z -> z
  
  val pow_pos : z -> positive -> z
  
  val pow : z -> z -> z
  
  val square : z -> z
  
  val compare : z -> z -> comparison
  
  val sgn : z -> z
  
  val leb : z -> z -> bool
  
  val ltb : z -> z -> bool
  
  val geb : z -> z -> bool
  
  val gtb : z -> z -> bool
  
  val eqb : z -> z -> bool
  
  val max : z -> z -> z
  
  val min : z -> z -> z
  
  val abs : z -> z
  
  val abs_nat : z -> nat
  
  val abs_N : z -> n
  
  val to_nat : z -> nat
  
  val to_N : z -> n
  
  val of_nat : nat -> z
  
  val of_N : n -> z
  
  val to_pos : z -> positive
  
  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pos_div_eucl : positive -> z -> (z, z) prod
  
  val div_eucl : z -> z -> (z, z) prod
  
  val div : z -> z -> z
  
  val modulo : z -> z -> z
  
  val quotrem : z -> z -> (z, z) prod
  
  val quot : z -> z -> z
  
  val rem : z -> z -> z
  
  val even : z -> bool
  
  val odd : z -> bool
  
  val div2 : z -> z
  
  val quot2 : z -> z
  
  val log2 : z -> z
  
  val sqrtrem : z -> (z, z) prod
  
  val sqrt : z -> z
  
  val gcd : z -> z -> z
  
  val ggcd : z -> z -> (z, (z, z) prod) prod
  
  val testbit : z -> z -> bool
  
  val shiftl : z -> z -> z
  
  val shiftr : z -> z -> z
  
  val coq_lor : z -> z -> z
  
  val coq_land : z -> z -> z
  
  val ldiff : z -> z -> z
  
  val coq_lxor : z -> z -> z
  
  val eq_dec : z -> z -> sumbool
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val leb_spec0 : z -> z -> reflect
  
  val ltb_spec0 : z -> z -> reflect
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  val sqrt_up : z -> z
  
  val log2_up : z -> z
  
  module Private_NZDiv : 
   sig 
    
   end
  
  module Private_Div : 
   sig 
    module Quot2Div : 
     sig 
      val div : z -> z -> z
      
      val modulo : z -> z -> z
     end
    
    module NZQuot : 
     sig 
      
     end
   end
  
  val lcm : z -> z -> z
  
  val eqb_spec : z -> z -> reflect
  
  val b2z : bool -> z
  
  val setbit : z -> z -> z
  
  val clearbit : z -> z -> z
  
  val lnot : z -> z
  
  val ones : z -> z
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : z -> z -> sumbool
    
    val min_case_strong :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : z -> z -> sumbool
   end
  
  val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : z -> z -> sumbool
  
  val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : z -> z -> sumbool
 end

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

type 't decEq =
  't -> 't -> sumbool
  (* singleton inductive, whose constructor was Build_DecEq *)

val eqdec : 'a1 decEq -> 'a1 -> 'a1 -> sumbool

type ('a, 'r) csymmetric = 'a -> 'a -> 'r -> 'r

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Cons0 of 'a * 'a stream

val hd : 'a1 stream -> 'a1

val tl : 'a1 stream -> 'a1 stream

val map0 : ('a1 -> 'a2) -> 'a1 stream -> 'a2 stream

val zipWith : ('a1 -> 'a2 -> 'a3) -> 'a1 stream -> 'a2 stream -> 'a3 stream

type ('a, 'b) cast = 'a -> 'b

val cast0 : ('a1, 'a2) cast -> 'a1 -> 'a2

type 'a plus0 = 'a -> 'a -> 'a

val plus1 : 'a1 plus0 -> 'a1 -> 'a1 -> 'a1

type 'a mult = 'a -> 'a -> 'a

val mult0 : 'a1 mult -> 'a1 -> 'a1 -> 'a1

type 'a one0 = 'a

val one1 : 'a1 one0 -> 'a1

type 'a zero0 = 'a

val zero1 : 'a1 zero0 -> 'a1

type 'a negate = 'a -> 'a

val negate0 : 'a1 negate -> 'a1 -> 'a1

type 'r nonNeg = 'r

type decision = sumbool

val decide : decision -> sumbool

val decide_rel : ('a1 -> 'a2 -> decision) -> 'a1 -> 'a2 -> decision

type rSetoid =
| Build_RSetoid

type st_car = __

type ('a, 'r) cotransitive = 'a -> 'a -> 'r -> 'a -> ('r, 'r) sum

type ('a, 'ap) is_CSetoid = { ax_ap_symmetric : ('a, 'ap) csymmetric;
                              ax_ap_cotransitive : ('a, 'ap) cotransitive }

type cSetoid = { cs_crr : rSetoid; cs_proof : (st_car, __) is_CSetoid }

val cs_crr : cSetoid -> rSetoid

type cs_ap = __

val build_CSetoid : ('a1, 'a2) is_CSetoid -> cSetoid

type bin_fun_strext =
  st_car -> st_car -> st_car -> st_car -> cs_ap -> (cs_ap, cs_ap) sum

type cSetoid_bin_fun = { csbf_fun : (st_car -> st_car -> st_car);
                         csbf_strext : bin_fun_strext }

val csbf_fun :
  cSetoid -> cSetoid -> cSetoid -> cSetoid_bin_fun -> st_car -> st_car ->
  st_car

type cSetoid_bin_op = cSetoid_bin_fun

type cSemiGroup = { csg_crr : cSetoid; csg_op : cSetoid_bin_op }

val csg_op : cSemiGroup -> cSetoid_bin_op

type ('a, 'b) sqrtFun = 'a -> 'b

val sqrtFun0 : ('a1, 'a2) sqrtFun -> 'a1 -> 'a2

type 'r realNumberPi = 'r

val __U03c0_ : 'a1 realNumberPi -> 'a1

type 'r halfNum = 'r

val half_num : 'a1 halfNum -> 'a1

type ('a, 'b) normSpace = 'a -> 'b

val norm : ('a1, 'a2) normSpace -> 'a1 -> 'a2

type 't cart2D = { x : 't; y : 't }

val x : 'a1 cart2D -> 'a1

val y : 'a1 cart2D -> 'a1

type 't polar2D = { rad : 't; __U03b8_ : 't }

val rad : 'a1 polar2D -> 'a1

val __U03b8_ : 'a1 polar2D -> 'a1

val normSpace_instance_Cart2D :
  ('a1, 'a2) sqrtFun -> 'a1 plus0 -> 'a1 mult -> ('a1 cart2D, 'a2) normSpace

type q = { qnum : z; qden : positive }

val qnum : q -> z

val qden : q -> positive

val inject_Z : z -> q

val qcompare : q -> q -> comparison

val qeq_dec : q -> q -> sumbool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val qlt_le_dec : q -> q -> sumbool

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

val qred : q -> q

val qminus' : q -> q -> q

val qabs : q -> q

val qfloor : q -> z

val ap_Q_cotransitive0 : q -> q -> q -> (__, __) sum

val qplus_strext0 : q -> q -> q -> q -> (__, __) sum

val ap_Q_cotransitive1 : q -> q -> q -> (__, __) sum

val ap_Q_is_apartness : (q, __) is_CSetoid

val q_as_CSetoid : cSetoid

val q_is_Setoid : rSetoid

val qplus_strext1 :
  st_car -> st_car -> st_car -> st_car -> (cs_ap, cs_ap) sum

val qplus_is_bin_fun : cSetoid_bin_fun

val q_as_CSemiGroup : cSemiGroup

type ('s, 'i, 'o) msgHandlerType = 's -> 'i -> ('s, 'o) prod

type ('in0, 'out) process = { curState : __;
                              handler : (__, 'in0, 'out) msgHandlerType }

type qpos = q

val qposMake : positive -> positive -> qpos

val qposAsQ : qpos -> q

val mkQpos : q -> qpos

val qpos_one : qpos

val qpos_mult : qpos -> qpos -> qpos

val qpos_inv : qpos -> qpos

val qabsQpos : q -> qpos

type 'rT rosTopicType =
| Build_RosTopicType

type 'rT topicType = __

type header =
  q
  (* singleton inductive, whose constructor was mkHeader *)

type 'rosTopic message = (('rosTopic, 'rosTopic topicType) sigT, header) prod

val transport : 'a1 -> 'a1 -> 'a2 -> 'a2

val getPayloadR :
  'a1 decEq -> 'a1 rosTopicType -> 'a1 -> ('a1, 'a1 topicType) sigT -> 'a1
  topicType option

val getPayload :
  'a1 decEq -> 'a1 rosTopicType -> 'a1 -> 'a1 message -> 'a1 topicType option

val mkDelayedMesg :
  'a1 decEq -> 'a1 rosTopicType -> 'a1 -> q -> 'a1 topicType -> 'a1 message

type 'rosTopic pureProcWDelay =
  'rosTopic topicType -> (q, 'rosTopic topicType) prod list

val delayedLift2Mesg :
  'a1 decEq -> 'a1 rosTopicType -> 'a1 -> 'a1 -> 'a1 pureProcWDelay -> 'a1
  message -> 'a1 message list

module Default : 
 sig 
  val min : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1
  
  val min_case :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) ->
    'a2
  
  val max : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1
  
  val max_case :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) ->
    'a2
 end

val qlt_le_dec_fast : q -> q -> sumbool

val qle_total : q -> q -> sumbool

val qmin : q -> q -> q

val qmax : q -> q -> q

type qposInf =
| Qpos2QposInf of qpos
| QposInfinity

val qposInf_bind : (qpos -> qposInf) -> qposInf -> qposInf

val qposInf_mult : qposInf -> qposInf -> qposInf

type metricSpace =
  rSetoid
  (* singleton inductive, whose constructor was Build_MetricSpace *)

val ball_ex_dec :
  metricSpace -> (qpos -> st_car -> st_car -> sumbool) -> qposInf -> st_car
  -> st_car -> sumbool

type uniformlyContinuousFunction = { ucFun : (st_car -> st_car);
                                     mu : (qpos -> qposInf) }

val ucFun :
  metricSpace -> metricSpace -> uniformlyContinuousFunction -> st_car ->
  st_car

val mu :
  metricSpace -> metricSpace -> uniformlyContinuousFunction -> qpos ->
  qposInf

val uc_Setoid : metricSpace -> metricSpace -> rSetoid

val uniformlyContinuousSpace : metricSpace -> metricSpace -> metricSpace

val ucFun2 :
  metricSpace -> metricSpace -> metricSpace -> st_car -> st_car -> st_car ->
  st_car

val uc_compose :
  metricSpace -> metricSpace -> metricSpace -> st_car -> st_car -> st_car

type decidableMetric = qpos -> st_car -> st_car -> sumbool

type regularFunction =
  qposInf -> st_car
  (* singleton inductive, whose constructor was Build_RegularFunction *)

val approximate : metricSpace -> regularFunction -> qposInf -> st_car

val regFun_Setoid : metricSpace -> rSetoid

val complete : metricSpace -> metricSpace

val cunit_fun : metricSpace -> st_car -> st_car

val cunit : metricSpace -> st_car

val cmap_fun : metricSpace -> metricSpace -> st_car -> st_car -> st_car

val cmap : metricSpace -> metricSpace -> st_car -> st_car

val cap_raw :
  metricSpace -> metricSpace -> st_car -> st_car -> qposInf -> st_car

val cap_fun : metricSpace -> metricSpace -> st_car -> st_car -> st_car

val cap_modulus : metricSpace -> metricSpace -> st_car -> qpos -> qposInf

val cap_weak : metricSpace -> metricSpace -> st_car -> st_car

val cap : metricSpace -> metricSpace -> st_car

val cmap2 : metricSpace -> metricSpace -> metricSpace -> st_car -> st_car

val q_as_MetricSpace : metricSpace

val qmetric_dec : decidableMetric

val qball_ex_bool : qposInf -> st_car -> st_car -> bool

val lt_dec : ('a1 -> 'a1 -> decision) -> 'a1 -> 'a1 -> decision

val nonNeg_inject : 'a1 zero0 -> ('a1 nonNeg, 'a1) cast

val q_0 : q zero0

val q_1 : q one0

val q_opp : q negate

val q_plus : q plus0

val q_mult : q mult

val decision_instance_0 : q -> q -> decision

val inject_Z_Q : (z, q) cast

val decision_instance_1 : q -> q -> decision

val cR : metricSpace

val inject_Q_CR : (q, st_car) cast

val qtranslate_uc : st_car -> st_car

val qplus_uc : st_car

val cRplus_uc : st_car

val cRplus : st_car plus0

val qopp_uc : st_car

val cRopp : st_car negate

val qboundBelow_uc : st_car -> st_car

val qboundAbove_uc : st_car -> st_car

val qscale_modulus : q -> qpos -> qposInf

val qscale_uc : st_car -> st_car

val scale : q -> st_car

val qboundAbs : qpos -> st_car

val qmult_modulus : qpos -> qpos -> qposInf

val qmult_uc : qpos -> st_car

val cRmult_bounded : qpos -> st_car

val cR_b : qpos -> st_car -> qpos

val cRmult : st_car mult

val approximateQ : q -> positive -> q

val root_step : q -> q -> q

val initial_root : q -> q

val root_loop : q -> qpos -> nat -> q -> positive -> q

val sqrt_raw : q -> qposInf -> q

val rational_sqrt_mid : q -> st_car

val rational_sqrt_big_bounded : nat -> q -> st_car

val rational_sqrt_small_bounded : nat -> q -> st_car

val rational_sqrt_pos : q -> st_car

val rational_sqrt : q -> st_car

val iterate : ('a1 -> 'a1) -> 'a1 -> 'a1 stream

val takeUntil :
  ('a1 stream -> bool) -> 'a1 stream -> ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a2

val everyOther : 'a1 stream -> 'a1 stream

val mult_Streams : 'a1 mult -> 'a1 stream -> 'a1 stream -> 'a1 stream

val powers_help : 'a1 mult -> 'a1 -> 'a1 -> 'a1 stream

val partialAlternatingSumUntil : (q stream -> bool) -> q stream -> q

val infiniteAlternatingSum_raw : q stream -> qposInf -> q

val infiniteAlternatingSum : q stream -> st_car

val ppositives_help : positive -> positive stream

val ppositives : positive stream

val qrecip_positives : q stream

val arctanSequence : q -> q stream

val rational_arctan_small_pos : q -> st_car

val rational_arctan_small : q -> st_car

val r_pi : q -> st_car

val cRpi : st_car

val rational_arctan_big_pos : q -> st_car

val rational_arctan_mid_pos : q -> st_car

val rational_arctan_pos : q -> st_car

val rational_arctan : q -> st_car

val qabs_uc : st_car

val cRabs : st_car

val rational_sqrt_SqrtFun_instance : (q, st_car) sqrtFun

val normSpace_instance_0 : (st_car, st_car) normSpace

val cRpi_RealNumberPi_instance : st_car realNumberPi

val q_Half_instance : q halfNum

val qSign : 'a1 negate -> q -> 'a1 -> 'a1

val q2Zapprox : q -> z

val r2ZApprox : st_car -> qpos -> z

val cast_instance_0 : (positive, st_car) cast

val simpleApproximate : st_car -> positive -> qpos -> q

val qSignHalf : q -> q

val polarTheta : q cart2D -> st_car

val polar__U03b8_Sign : q cart2D -> q

val cart2Polar : q cart2D -> st_car polar2D

val robotPureProgam :
  qpos -> qpos -> qpos -> qpos -> positive -> q cart2D -> (q, q polar2D) prod
  list

type topic =
| VELOCITY
| TARGETPOS

val topic_beq : topic -> topic -> bool

val topic_eq_dec : topic -> topic -> sumbool

val ldskflskdalfkTopic_eq_dec : topic decEq

val ttttt : topic rosTopicType

val rotSpeedRadPerSec : qpos

val speedMetresPerSec : qpos

val delResSecInv : positive

val delEpsSec : qpos

val initDelayLin : qpos

val robotProgramInstance : qpos -> topic pureProcWDelay

val swProcessInstance : (topic message, topic message list) process

val target1Metres : q cart2D

val robotOutput : (q, q polar2D) prod list

val projNums : (q, q polar2D) prod -> ((z, z) prod, z) prod

val robotOutputInts : ((z, z) prod, z) prod list

val map3 :
  ('a1 -> 'a2) -> (('a1, 'a1) prod, 'a1) prod -> (('a2, 'a2) prod, 'a2) prod

