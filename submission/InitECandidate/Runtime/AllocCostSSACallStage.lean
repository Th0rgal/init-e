import InitECandidate.Runtime.AllocCostSSAAllocationTransfer
import InitECandidate.Runtime.AllocCostSSANativeCall

/-!
# Returning-call cost decomposition and allocator-relation call stage

`wordExecutionCost` charges a returning call as its own node price plus the
callee-body run plus, when the callee returns the call's arity and the popped
environment unions consistently, the return-handler continuation.  This module

* proves that decomposition as an explicit equation, price-generic
  (`wec_call_returning_result_unfold`), reading the literal call clause at the
  actual reached states;
* states the corresponding allocator stage theorem
  (`ssaCall_returning_cost_stage`): for `SsaAllocRel`-related source and
  allocated states, the allocated returning call costs no more than the source
  call, from the local call-node price comparison plus the callee-body and
  return-handler transfers.  No whole target-run cost is assumed.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordAlloc
open InitECandidate.Runtime.WordToStack

/-- **Returning-call stage decomposition at the allocator relation.**

For source and allocated call states related by `SsaAllocRel` (the original
allocator relation: every machine field equal, allocated locals the SSA
renaming), the allocated returning call costs no more than the source call as
soon as the three components of the model's own call clause compare locally:

* the call node price (`nodeT <= nodeS`),
* the callee-body run at the allocated entry versus the source entry
  (`bodyT <= bodyS`; the allocated entry's cost is transferred to the source
  entry by `nativeWordPrice_callBody_transfer` whenever the stacks are
  `sValEq`-related),
* the return-handler continuation at the allocated popped state versus the
  source popped state (`contT <= contS`; transferred by
  `nativeWordPrice_returnContinuation_transfer`).

The two call-cost equations are the model clause at the actual reached branch
(`result` and `exception` respectively); no whole target-run cost is assumed,
and no budget is supplied for the target side. -/
theorem ssaCall_returning_cost_stage {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s t : WordSemStateFiniteExact 64 C F) (rel : SsaAllocRel ssa next s t)
    (nodeT nodeS bodyT bodyS contT contS : Nat)
    (hcallT : wordExecutionCost nativeWordPrice
      (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
        nodeT + bodyT + contT)
    (hcallS : wordExecutionCost nativeWordPrice
      (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
        nodeS + bodyS + contS)
    (hnode : nodeT ≤ nodeS) (hbody : bodyT ≤ bodyS) (hcont : contT ≤ contS) :
    wordExecutionCost nativeWordPrice
        (.call (some (values, names, retCode, l1, l2)) dest args handler) t ≤
      wordExecutionCost nativeWordPrice
        (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  rw [hcallT, hcallS]
  omega

/-- The callee-body component at the allocated entry, transferred to the source
entry: the allocated calling convention builds the entry from a stack that is
`sValEq`-related to the source one, which is exactly the entry condition of the
checked `nativeWordPrice_callBody_transfer`. -/
theorem ssaCall_body_stage {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s t : WordSemStateFiniteExact 64 C F) (rel : SsaAllocRel ssa next s t)
    (ys : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq t.stack ys)
    (hne : (evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))).1 ≠
        some WordSemResult.error) :
    wordExecutionCost nativeWordPrice prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (decClock { s with stack := ys }))) =
      wordExecutionCost nativeWordPrice prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (decClock s))) := by
  have hvalS : WordSemStackEq.sValEq s.stack ys := by
    rw [← stage_stack rel]
    exact hval
  exact nativeWordPrice_callBody_transfer prog args1 ss envs handler s ys hvalS hne

/-- The return-handler continuation component: the allocated continuation runs
on the popped environment with a stack that is `sValEq`-related to the source
one, which is exactly the hypothesis of the checked
`nativeWordPrice_returnContinuation_transfer`. -/
theorem ssaCall_continuation_stage {C F : Type}
    (values : List Nat) (returned : List (WordLocW 64))
    (retCode : WordLangProgHOL (BitVec 64))
    (popped : WordSemStateFiniteExact 64 C F)
    (ys : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq popped.stack ys)
    (hne : (evaluate retCode
      (WordSemStateFiniteExact.setVars values returned popped)).1 ≠
        some WordSemResult.error) :
    wordExecutionCost nativeWordPrice retCode
        { WordSemStateFiniteExact.setVars values returned popped with stack := ys } =
      wordExecutionCost nativeWordPrice retCode
        (WordSemStateFiniteExact.setVars values returned popped) := by
  have hval' : WordSemStackEq.sValEq
      (WordSemStateFiniteExact.setVars values returned popped).stack ys := hval
  exact nativeWordPrice_returnContinuation_transfer retCode
    (WordSemStateFiniteExact.setVars values returned popped) ys hval' hne

#print axioms ssaCall_returning_cost_stage
#print axioms ssaCall_body_stage
#print axioms ssaCall_continuation_stage

end InitECandidate.Runtime.FineCost
