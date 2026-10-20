import InitECandidate.Runtime.WordPathWork
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap

/-!
# Cost invariance of `wordPathWork` under a value-equal stack swap

`wordPathWork` unfolds by structural recursion on the program and inspects the
state only through

* `locals` (`getVar`, `getVars`, `cutState`, `wordSemCutEnvs`),
* `code`, `stackSize` (the `wordSemFindCode` of a call),
* `clock`, `termdep`,
* the *frames pushed by the call itself* (via `pushEnv` from the cut
  environments) and the `popEnv` of those same frames at return.

The saved caller frames differ between the source and the renamed target only in
their environment keys, and they are never read: a returning callee exits before
the parent frame is popped, and the pop that rebuilds the caller's locals uses
the frame pushed by *this* call, which is built from the same cut environments
on both sides.  Hence the cost is invariant under replacing the stack by any
`WordSemStackEq.sValEq`-related stack (`stackSwapPost` is already stated in
terms of `sValEq`, so evaluation transports the result and non-stack fields).

This module collects the commuting lemmas for that proof; the main induction is
`wordPathWork_sValEq_stack_variant`.
-/

namespace InitECandidate.Runtime.WordToStack

open Flapjack Flapjack.WordSemStateFiniteExact

/-- `getVar` reads only the locals. -/
theorem getVar_stack {C F : Type} (name : Nat) (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) :
    getVar name { s with stack := xs } = getVar name s := rfl

/-- `getVars` reads only the locals. -/
theorem getVars_stack {C F : Type} :
    ∀ (args : List Nat) (s : WordSemStateFiniteExact 64 C F)
      (xs : List (WordSemStackFrame 64)),
      WordSemStateFiniteExact.getVars args { s with stack := xs } =
        WordSemStateFiniteExact.getVars args s
  | [], _, _ => rfl
  | _ :: vs, s, xs => by
      simp only [WordSemStateFiniteExact.getVars, getVar_stack, getVars_stack vs]

/-- `getVarImm` reads only the locals. -/
theorem getVarImm_stack {C F : Type} (operand : WordRegImm (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)) :
    getVarImm operand { s with stack := xs } = getVarImm operand s := by
  cases operand with
  | reg n => rfl
  | imm w => rfl

/-- Cutting a state touches only the locals, so it commutes with a stack swap. -/
theorem cutState_stack {C F : Type} (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)) :
    cutState names { s with stack := xs } =
      (match cutState names s with
        | none => none
        | some c => some { c with stack := xs }) := by
  unfold WordSemStateFiniteExact.cutState
  cases wordSemCutEnv names s.locals with
  | none => rfl
  | some env => rfl

/-- `decClock` touches only the clock. -/
theorem decClock_stack {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) :
    decClock { s with stack := xs } = { decClock s with stack := xs } := rfl

/-- `setVar` touches only the locals. -/
theorem setVar_stack {C F : Type} (name : Nat) (value : WordLocW 64)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)) :
    setVar name value { s with stack := xs } = { setVar name value s with stack := xs } :=
  rfl

/-- `setVars` touches only the locals. -/
theorem setVars_stack {C F : Type} (names : List Nat) (values : List (WordLocW 64))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)) :
    setVars names values { s with stack := xs } =
      { setVars names values s with stack := xs } := rfl

#print axioms getVar_stack
#print axioms getVars_stack
#print axioms getVarImm_stack
#print axioms cutState_stack
#print axioms decClock_stack
#print axioms setVar_stack
#print axioms setVars_stack

end InitECandidate.Runtime.WordToStack
