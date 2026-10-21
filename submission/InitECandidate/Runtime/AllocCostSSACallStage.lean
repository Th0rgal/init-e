import InitECandidate.Runtime.AllocCostSSAAllocationTransfer
import InitECandidate.Runtime.AllocCostSSANativeCall

/-!
# Returning-call cost decomposition and allocator-relation call stage

`wordExecutionCost` charges a returning call as its own node price plus the
callee-body run plus, when the callee returns the call's arity and the popped
environment unions consistently, the return-handler continuation.  This module

* records that decomposition as the model clause at the actual reached branch
  (`ssaCall_returning_cost_stage` takes the two call-cost equations, one per
  branch);
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

/-- **Direct returning-call decomposition.**  At the actual reached states the
literal call clause is its node price plus the callee-body run plus the
return-handler continuation.  The program is the explicit `.call (some …)`
form, the root node price is first generalised to an opaque `localPrice` (a
definitional alias, so no case split can select the `wordCallReturned`
predicate hidden inside the price term), and the known discriminants are then
rewritten one at a time with `dsimp only` reducing the resulting concrete
matches. -/
theorem wec_call_returning_result_unfold {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (vals0 : List (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle popped : WordSemStateFiniteExact 64 C F)
    (hget : getVars args s = some vals0)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0) s.code s.stackSize =
        some (args1, prog, ss))
    (hdom : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names s.locals = some envs)
    (hz : s.clock ≠ 0)
    (hrun : fixClock
      (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog
        (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))) =
          (some (.result location returned), middle))
    (hloc : location = .loc l1 l2)
    (hlen : returned.length = values.length)
    (hpop : popEnv middle = some popped)
    (hdu : sptDomainEqUnion popped.locals envs.1 envs.2) :
    wordExecutionCost price
        (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      price (.call (some (values, names, retCode, l1, l2)) dest args handler) s +
        wordExecutionCost price prog
          (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) +
        wordExecutionCost price retCode
          (WordSemStateFiniteExact.setVars values returned popped) := by
  have hcond : ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) := by
    simp [hloc, hlen]
  rw [wordExecutionCost]
  generalize hLocal : price (.call (some (values, names, retCode, l1, l2)) dest args handler) s
    = localPrice
  rw [hget]; try dsimp only
  rw [hbad]; try dsimp only
  rw [hfind]; try dsimp only
  simp only [hdom]; try dsimp only
  rw [hcut]; try dsimp only [wordSemCutEnvs]
  rw [dif_neg hz]; try dsimp only
  rw [hrun]; try dsimp only
  simp only [hcond]; try dsimp only
  rw [hpop]; try dsimp only
  simp only [hdu]; try dsimp only
  rfl

/-- **Direct exception-branch decomposition.**  When the callee raises at the
declared handler label and the raised environment unions consistently, the call
cost is the node price plus the callee-body run plus the return-handler code run
on `setVar reg value middle`.  The handler payload is destructed explicitly by
taking the handler as `some (reg, handlerCode, h1, h2)`, and the callee entry
state appears as an explicit parameter so the premise stays readable. -/
theorem wec_call_returning_exception_unfold {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (s entry : WordSemStateFiniteExact 64 C F) (vals0 : List (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location value : WordLocW 64)
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : getVars args s = some vals0)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0) s.code s.stackSize =
        some (args1, prog, ss))
    (hdom : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names s.locals = some envs)
    (hz : s.clock ≠ 0)
    (hentry : entry = WordSemStateFiniteExact.callEnv args1 ss
      (pushEnv envs (some (reg, handlerCode, h1, h2)) (decClock s)))
    (hrun : fixClock entry (evaluate prog entry) =
      (some (.exception location value), middle))
    (hloc : location = .loc h1 h2)
    (hdu : sptDomainEqUnion middle.locals envs.1 envs.2) :
    wordExecutionCost price
        (.call (some (values, names, retCode, l1, l2)) dest args
          (some (reg, handlerCode, h1, h2))) s =
      price (.call (some (values, names, retCode, l1, l2)) dest args
          (some (reg, handlerCode, h1, h2))) s +
        wordExecutionCost price prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs (some (reg, handlerCode, h1, h2)) (decClock s))) +
        wordExecutionCost price handlerCode
          (WordSemStateFiniteExact.setVar reg value middle) := by
  have hcond : ¬ (location ≠ .loc h1 h2) := by simp [hloc]
  rw [wordExecutionCost]
  generalize hLocal : price (.call (some (values, names, retCode, l1, l2)) dest args
    (some (reg, handlerCode, h1, h2))) s = localPrice
  rw [hget]; try dsimp only
  rw [hbad]; try dsimp only
  rw [hfind]; try dsimp only
  simp only [hdom]; try dsimp only
  rw [hcut]; try dsimp only [wordSemCutEnvs]
  rw [dif_neg hz]; try dsimp only
  rw [← hentry]
  rw [hrun]; try dsimp only
  simp only [hcond]; try dsimp only
  simp only [hdu]; try dsimp only
  rfl

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

/-- The callee-body component at the allocated entry: the stack condition is
derived from `SsaAllocRel` itself (`stage_sValEq`), so no caller-supplied
`sValEq` is needed. -/
theorem ssaCall_body_stage {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s t : WordSemStateFiniteExact 64 C F) (rel : SsaAllocRel ssa next s t)
    (hne : (evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))).1 ≠
        some WordSemResult.error) :
    wordExecutionCost nativeWordPrice prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (decClock { s with stack := t.stack }))) =
      wordExecutionCost nativeWordPrice prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (decClock s))) :=
  nativeWordPrice_callBody_transfer prog args1 ss envs handler s t.stack
    (stage_sValEq rel) hne

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

#print axioms wec_call_returning_result_unfold

/-- **Return-handler stage leg at the allocator relation.**  The exception
branch of a returning call obeys the same stage inequality: for
`SsaAllocRel`-related states the allocated call costs no more than the source
call as soon as the node price, the callee-body run and the handler-code run
compare locally.  This is the return-handler counterpart of
`ssaCall_returning_cost_stage`. -/
theorem ssaCall_exception_cost_stage {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (s t : WordSemStateFiniteExact 64 C F) (rel : SsaAllocRel ssa next s t)
    (nodeT nodeS bodyT bodyS contT contS : Nat)
    (hcallT : wordExecutionCost nativeWordPrice
      (.call (some (values, names, retCode, l1, l2)) dest args
        (some (reg, handlerCode, h1, h2))) t = nodeT + bodyT + contT)
    (hcallS : wordExecutionCost nativeWordPrice
      (.call (some (values, names, retCode, l1, l2)) dest args
        (some (reg, handlerCode, h1, h2))) s = nodeS + bodyS + contS)
    (hnode : nodeT ≤ nodeS) (hbody : bodyT ≤ bodyS) (hcont : contT ≤ contS) :
    wordExecutionCost nativeWordPrice
        (.call (some (values, names, retCode, l1, l2)) dest args
          (some (reg, handlerCode, h1, h2))) t ≤
      wordExecutionCost nativeWordPrice
        (.call (some (values, names, retCode, l1, l2)) dest args
          (some (reg, handlerCode, h1, h2))) s := by
  rw [hcallT, hcallS]
  omega

#print axioms wec_call_returning_exception_unfold
#print axioms ssaCall_returning_cost_stage
#print axioms ssaCall_exception_cost_stage
#print axioms ssaCall_body_stage
#print axioms ssaCall_continuation_stage

end InitECandidate.Runtime.FineCost
