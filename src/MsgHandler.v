Require Import Coq.Unicode.Utf8.
Require Export StdlibMisc.
(** printing → $\rightarrow$ #→# *)
(** printing × $\times$ #×# *)

Set Implicit Arguments.
Require Import CoList.


Definition MsgHandlerType (S I O : Type) := S → I → (S × O).

Require Export Coq.Lists.List.

CoFixpoint outMsgsAux {S I O : Type} (st : S) (mh : MsgHandlerType S I O)
           (ins : CoList I) : CoList O :=
  match ins with
    | cnil _ => cnil O
    | ccons h tl => let (ns,out) := (mh st h) in
                    ccons out (outMsgsAux ns mh tl)
  end.
    

Definition mkPureHandler {In Out} 
 (f : In → Out) : MsgHandlerType unit In Out :=
 λ st inp, (st, f inp).


Record Process (In Out : Type) :Type := { 
  State : Type;
  curState : State;
  handler : MsgHandlerType State In Out
}.

Definition procOutMsgs {I O : Type} (p : Process I O)
           (ins : CoList I) : CoList O :=
  outMsgsAux (curState p) (handler p) ins.


Definition getOutput {In Out : Type}
  (p: Process In Out) (inp : In ): Out :=
 snd ((handler p) (curState p) inp).

Definition applyProc {In Out : Type}
  (p: Process In Out) (inp : In ): (State p) * Out :=
((handler p) (curState p) inp).

Definition updateState {In Out : Type}
  (p: Process In Out) (state : State p)
 := {| State := State p; curState := state; handler := handler p|}.


Definition getNewProc {In Out : Type}
  (p: Process In Out) (inp : In ): Process In Out :=
updateState p (fst ((handler p) (curState p) inp)).


(* outermost event is the last event *)
Fixpoint getNewProcL  {In Out : Type}
  (p: Process In Out) (linp : list In ): Process In Out :=
match linp with
| nil => p
| hi::tli => getNewProc (getNewProcL p tli) hi
end.


Definition mkPureProcess {In Out} 
 (f : In -> Out) : Process In Out :=
{| State := _; curState := tt; handler := mkPureHandler f|}.


Lemma getNewProcLPure : forall
    {In Out : Type}
    (f : In -> Out)
    (prefix : list In),
  getNewProcL (mkPureProcess f) prefix = (mkPureProcess f).
Proof.
  induction prefix; simpl;[ reflexivity| ].
  rewrite IHprefix.
  unfold getNewProc.
  simpl. reflexivity.
Qed.


Definition getLastOutput  {In Out : Type}
    (p: Process In Out) 
    (prefix : list In) 
    (last : In) : Out :=
  let procBeforeLast := getNewProcL p prefix in
  getOutput procBeforeLast last.

Lemma getLastOutputPure : forall
    {In Out : Type}
    (f : In -> Out)
    (prefix : list In)
    (last : In),
  getLastOutput (mkPureProcess f) prefix last
  = f last.
Proof.
  intros.
  unfold getLastOutput.
  rewrite getNewProcLPure.
  reflexivity.
Qed.


Definition getLastOutputL  {In Out : Type}
    (p: Process In (list Out)) 
    (allInputs : list In)  : list Out :=
    match allInputs with
    | nil => nil
    | last :: rest => getLastOutput p rest last
    end.


