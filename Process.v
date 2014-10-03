Set Implicit Arguments.


CoInductive Process (In Out : Type) :=
buildP : (In -> ((Process In Out)* Out))
          -> Process In Out.


Definition getOutput {In Out : Type}
  (p: Process In Out) (inp : In ): Out :=

match p with
| buildP f => snd (f inp)
end.

Definition getNewProc {In Out : Type}
  (p: Process In Out) (inp : In ): Process In Out :=
match p with
| buildP f => fst (f inp)
end.

Require Export Coq.Lists.List.

Fixpoint getNewProcL  {In Out : Type}
  (p: Process In Out) (linp : list In ): Process In Out :=
match linp with
| nil => p
| hi::tli => getNewProcL (getNewProc p hi) tli
end.

Definition getOutputL  {In Out : Type}
    (p: Process In Out) 
    (prefix : list In) 
    (last : In) : Out :=
  let procBeforeLast := getNewProcL p prefix in
  getOutput procBeforeLast last.


Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export core.


(** not relevant for code generation, 
    only relevant for reasoning *)

Section Dev.

Variable Env : Type.
  
(** Output devices receive messages and
    affect their environment. Examples are
    heating devices, motors in mobile robots
    like iCreate
    
    In our model,
    an output device receives a message and outputs
    a property about how future environment evolves.
    Note that the device can use the previous history of
    inputs.

    For example, when a roomba icreate receives
    a message with a request to go along X axis with
    speed 1m/s , the output property could be
    that the robots physical speed somewhere between
    0.9m/s and 1.1 m/s until a new message arrives
 *)
Definition OutDev (Inp : Type) :=
  Process Inp ((Time -> Env) -> Prop).

Definition MemoryLessOutDev (Inp : Type) :=
  Inp -> ((Time -> Env) -> Prop).

CoFixpoint makeOutDev {Inp: Type} 
  (m: MemoryLessOutDev Inp) : OutDev Inp :=
   buildP (fun inp : Inp => (makeOutDev m, m inp)).

Coercion makeOutDev : MemoryLessOutDev >-> OutDev.


(** An input device observes the environment over time
    and may emit messages.
    In the following model, it is a function which
    when given how environment evolved,
    either never outputs a message ([unit] case)
    our outputs a triple indicating the output message,
    time of output and a new device (possibly storing some state)

    Time is relative to the previous emitted message.
    If no message was emitted yet, time is relative to
    the instant the device (driver) was turned on.

    The reason why [InpDev] cannot be modeled
    by a software node is because unlike
    software nodes, input devices can emit
    messages even when they did not receive
    any input. Maybe we can generalize software
    nodes to do that. 
*)
CoInductive InpDev (Out : Type) :=
maybeSendMesg : 
      ((Time -> Env) 
        -> (unit + (Out * Time * InpDev Out)))
        -> InpDev Out.

End Dev.
