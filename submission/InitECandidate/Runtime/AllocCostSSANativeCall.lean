import InitECandidate.Runtime.AllocCostSSANativePrice

/-!
# Native-price call transfer and local call caps

The SSA returning-call alignment needs the callee body and the return-handler
continuation to cost the same on the allocated (stack-renamed) caller stack as
on the source one.  Both are instances of the native stack-variant transport
`wordExecutionCost_nativeWordPrice_stack_variant`, with the entry state built by
`callEnv`/`pushEnv` as in the actual call clause.

This module also records the *local* per-call caps of the native price: a call
node costs at most its own argument and return lists, never a whole-call or
whole-program budget.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-- A tail call pays its fixed jump overhead only. -/
theorem nativeWordPrice_tailcall_le {C F : Type} (dest : Option Nat)
    (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    nativeWordPrice (.call none dest arguments handler) s ≤ 41 := by
  rw [nativeWordPrice]

/-- A returning call pays its own argument and return lists, and the return part
only when the callee actually returns that arity. -/
theorem nativeWordPrice_call_le {C F : Type} (returns : List Nat)
    (cutset : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    nativeWordPrice (.call (some (returns, cutset, retCode, l1, l2)) dest arguments
      handler) s ≤ 189 + 39 * (arguments.length + 1 - 22) + 21 * returns.length := by
  rw [nativeWordPrice]
  split <;> omega

/-- **Callee-body transfer at the native price.**  The executed cost of a callee
body at the *stack-swapped* caller entry equals its cost at the source entry.
Discharged from the actual `callEnv`/`pushEnv` entry construction. -/
theorem nativeWordPrice_callBody_transfer {C F : Type}
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (ys : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq s.stack ys)
    (hne : (evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))).1 ≠
        some WordSemResult.error) :
    wordExecutionCost nativeWordPrice prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (decClock { s with stack := ys }))) =
      wordExecutionCost nativeWordPrice prog
        (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) := by
  obtain ⟨ys2, hentry, hentryVal⟩ := callEnv_entry_swap args1 ss envs handler s ys hval
  rw [hentry]
  exact wordExecutionCost_nativeWordPrice_stack_variant prog
    (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))
    ys2 hentryVal hne

/-- **Return-continuation transfer at the native price.**  The return-handler
continuation costs the same on a value-equal (allocated) stack. -/
theorem nativeWordPrice_returnContinuation_transfer {C F : Type}
    (continuation : WordLangProgHOL (BitVec 64))
    (returned : WordSemStateFiniteExact 64 C F) (targetStack : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq returned.stack targetStack)
    (hne : (evaluate continuation returned).1 ≠ some WordSemResult.error) :
    wordExecutionCost nativeWordPrice continuation { returned with stack := targetStack } =
      wordExecutionCost nativeWordPrice continuation returned :=
  wordExecutionCost_nativeWordPrice_stack_variant continuation returned targetStack hval hne

#print axioms nativeWordPrice_tailcall_le
#print axioms nativeWordPrice_call_le
#print axioms nativeWordPrice_callBody_transfer
#print axioms nativeWordPrice_returnContinuation_transfer

end InitECandidate.Runtime.FineCost
