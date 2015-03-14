Set Implicit Arguments.


CoInductive Process (In Out : Type) :=
buildP (f : (In -> ((Process In Out) * Out))).

Require Import Coq.Unicode.Utf8.

CoFixpoint mkPureProcess {In Out} 
 (f : In -> Out) : Process In Out :=
buildP (λ inp, (mkPureProcess f, f inp)).

(* cofix works
Definition SPP1 := mkPureProcess (fun n:nat => 1).

Goal forall x, ((match SPP1 with
| buildP f =>  (f 0)
end) = x).
intros.
vm_compute.
*)

Definition getOutput {In Out : Type}
  (p: Process In Out) (inp : In ): Out :=
match p with
| buildP f => snd (f inp)
end.

Definition applyProc {In Out : Type}
  (p: Process In Out) (inp : In ): (Process In Out) * Out :=
match p with
| buildP f =>  (f inp)
end.

Definition getNewProc {In Out : Type}
  (p: Process In Out) (inp : In ): Process In Out :=
match p with
| buildP f => fst (f inp)
end.

Require Export Coq.Lists.List.

(* outermost event is the last event *)
Fixpoint getNewProcL  {In Out : Type}
  (p: Process In Out) (linp : list In ): Process In Out :=
match linp with
| nil => p
| hi::tli => getNewProc (getNewProcL p tli) hi
end.

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


Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
