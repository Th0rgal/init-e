import InitECandidate.Runtime.FullSSATableTailCost
import InitECandidate.Runtime.WordStackValueGlobalCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Compose actual compiled-callee execution with saved-stack-value transport.
The original caller stack and the renamed caller stack can have different keys;
we retain the real intermediate run on the renamed stack for later pop/unwind
proofs. The guarded compiler IH chooses one scheduler and stack transport
preserves its original source cost, including escaping exceptions. -/
theorem fullSSA_mapped_callee_stack_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (body : WordLangProgHOL (BitVec 64)) (count depth clock : Nat)
    (source target : WordSemStateFiniteExact 64 C F)
    (entry : {source with stack := target.stack,code := fullSSACodeTable source.code} = target)
    (values : WordSemStackEq.sValEq source.stack target.stack)
    (smaller : Prod.Lex (· < ·) (· < ·) (source.termdep,source.clock) (depth,clock))
    (bodyFree : noInstallSubprogsHOL body = true) (codeFree : WordProps.noInstallCode source.code)
    (domain : sptDomain source.locals = (fun key => key ∈ evenList count))
    (fit : let setup := setupSSA (outputWidth := 64) count (limitVar body) body;
      ssaCostFits SP TP body setup.2.1 setup.2.2 [])
    (ih : FullSSATableFunctionIH (C := C) (F := F) SP TP depth clock) :
    ∃ permutation : Nat → Nat → Nat,
      let originalState := {source with permute := permutation}
      let swappedState := {originalState with stack := target.stack}
      let original := evaluate body originalState
      let swapped := evaluate body swappedState
      let compiled := evaluate (fullSsaCcTrans count body) target
      original.1 = some .error ∨ original.1 = swapped.1 ∧ swapped.1 = compiled.1 ∧
        FullSSATableFrame swapped.2 compiled.2 ∧
        (match swapped.1 with
        | none => True
        | some (.break _) => True
        | some (.continue _) => True
        | some _ => swapped.2.locals = compiled.2.locals) ∧
        wordExecutionCost (fun p _ => TP p) (fullSsaCcTrans count body) target ≤
          wordExecutionCost (fun p _ => SP p) body originalState + fullSSAEntryPrice TP count body := by
  let switched := {source with stack := target.stack}
  have actualEntry : {switched with code := fullSSACodeTable switched.code} = target := entry
  obtain ⟨permutation,post⟩ := ih body count switched smaller bodyFree codeFree domain fit
  dsimp only at post
  rw [actualEntry] at post
  refine ⟨permutation,?_⟩
  by_cases safe : (evaluate body {source with permute := permutation}).1 = some .error
  · exact Or.inl safe
  · have same := stack_value_result body {source with permute := permutation} target.stack values safe
    have sameCost := word_stack_value_executed_cost SP body {source with permute := permutation}
      safe target.stack values
    change (evaluate body {switched with permute := permutation}).1 =
      (evaluate body {source with permute := permutation}).1 at same
    change wordExecutionCost (fun p (_ : WordSemStateFiniteExact 64 C F) => SP p) body
        {switched with permute := permutation} =
      wordExecutionCost (fun p _ => SP p) body {source with permute := permutation} at sameCost
    rcases post with error | ⟨result,frame,locals,cost⟩
    · exact (safe (same.symm.trans error)).elim
    · exact Or.inr ⟨same.symm,result,frame,locals,by simpa only [sameCost] using cost⟩

#print axioms fullSSA_mapped_callee_stack_cost
end InitECandidate.Runtime.FineCost
