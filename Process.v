
(** Abstract Locations *)
Class LocType (L : Type) :=
{
    mloc_eq_dec : forall x y : L, { x=y } + { ~ x<>y }
}.

(** Parametrized Message Type. Represents
    messages carrying payload of type PLT *)
Class PMesgType (MT PLT L: Type ) {ml : LocType L}:=
{
    getPayLoadPM : MT -> PLT;
    getDestPM : MT -> L;
    getSrcPM : MT -> L
}.

(** We remove the PLD parameter *)
Class MesgType (MT L: Type ) {ml : LocType L}:=
{
    PLT : Type;
    getPayLoadM : MT -> PLT;
    getDestM : MT -> L;
    getSrcM : MT -> L
}.


Class ProcessType (Prt L MT P)