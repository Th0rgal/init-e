import InitECandidate.Runtime.StackAllocExecutedCorrect
import InitECandidate.Runtime.StackAllocSelectedBudget

namespace InitECandidate.Runtime.StackAlloc
open Flapjack Flapjack.Compiler.Backend Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open InitECandidate.Runtime.StackToLab

/-- The allocation stage's actual initialized execution and executed-cost
bound. All source/target initialization overrides are discharged here. -/
theorem initialized_entry_executed_cost {C F : Type} (price : HolProg 64 → Nat)
    (code : List (Nat × HolProg 64))
    (oracle : Nat → C × List (Nat × HolProg 64) × List (BitVec 64))
    (s t : StackSemStateFiniteExact 64 C F) (c : DataToWord.Config) (entry : Nat)
    (result : Option (StackSemResult 64))
    (codeArgs : ∀ k p, sptAListLookup k code = some p → k ≠ gcStubLocation ∧ StackProps.allocArg p)
    (oracleArgs : ∀ n k p, (k, p) ∈ (oracle n).2.1 → k ≠ gcStubLocation ∧ StackProps.allocArg p)
    (stack : s.useStack = true) (store : s.useStore = true) (alloc : s.useAlloc ≠ true)
    (codeEq : s.code = sptFromAList (compile c code))
    (oracleEq : s.compileOracle = oracleMap ∘ oracle)
    (buf : BufBound s) (stackBound : StackBound s)
    (codeFree : allocationFreeCode code = true)
    (oracleFree : ∀ n, allocationFreeCode (oracle n).2.1 = true)
    (run : evaluate (.call none (.inl entry) none,
      makeInit c (sptFromAList code) oracle s) = (result, t))
    (notError : result ≠ some .error) :
    ∃ regs1, evaluate (.call none (.inl entry) none, s) =
      (result, Res s.gcFun s.compile c t regs1) ∧ Post result t regs1 ∧
      stackExecutionCost (fun p _ => price p) (.call none (.inl entry) none) s ≤
        stackExecutionCost (fun p _ => price p) (.call none (.inl entry) none)
          (makeInit c (sptFromAList code) oracle s) := by
  let source := makeInit c (sptFromAList code) oracle s
  have pre : Pre s.compile c source s.regs := by
    refine ⟨?_, oracleArgs, rfl, rfl, stackBound, ?_, rfl, buf, rfl⟩
    · intro key body lookup
      apply codeArgs key body
      change sptLookup key (sptFromAList code) = some body at lookup
      rwa [sptLookup_sptFromAList] at lookup
    · intro key value lookup
      exact lookup
  have free : FreeState source := by
    constructor
    · intro key body lookup
      change sptLookup key (sptFromAList code) = some body at lookup
      rw [sptLookup_sptFromAList] at lookup
      exact allocationFreeCode_member code codeFree (key, body) (sptAListLookup_mem _ _ _ lookup)
    · intro n key body member
      exact allocationFreeCode_member _ (oracleFree n) (key, body) member
  obtain ⟨regs1, targetRun, post, cost⟩ := ExecutedCost.allocationFree_executed_cost price s.gcFun s.compile
    (.call none (.inl entry) none) source t result c s.regs
    (by simp [allocationFree]) free run notError (by simp [StackProps.allocArg]) pre
  rw [res_makeInit_eq code oracle s c stack store alloc codeEq oracleEq] at targetRun cost
  exact ⟨regs1, targetRun, post, cost⟩


#print axioms initialized_entry_executed_cost
end InitECandidate.Runtime.StackAlloc
