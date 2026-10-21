import InitECandidate.Runtime.StackAllocInitializedExecutedCost

namespace InitECandidate.Runtime.StackAlloc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove.Proofs
open InitECandidate.Runtime.StackToLab

/-- A real selected stack-removal initializer supplies the allocation stage's
flags, code, oracle and bounds. Execution and cost transport reach this actual
selected state, rather than an abstract simulation state. -/
theorem selected_entry_executed_cost {C F : Type} (price : HolProg 64 → Nat)
    (c : DataToWord.Config) (code : List (Nat × HolProg 64))
    (oracle : Nat → C × List (Nat × HolProg 64) × List (BitVec 64))
    (generateGc : Bool) (maxHeap dataSpace pointer entry fuel : Nat)
    (bitmaps : List (BitVec 64)) (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (base source post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (codeArgs : ∀ k p, sptAListLookup k code = some p → k ≠ gcStubLocation ∧ StackProps.allocArg p)
    (oracleArgs : ∀ n k p, (k, p) ∈ (oracle n).2.1 → k ≠ gcStubLocation ∧ StackProps.allocArg p)
    (codeFree : allocationFreeCode code = true)
    (oracleFree : ∀ n, allocationFreeCode (oracle n).2.1 = true)
    (selected : InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace (oracleMap ∘ oracle)
      jump bounds pointer (sptFromAList (compile c code)) base = some source)
    (run : StackSemEvaluate.evaluate (.call none (.inl entry) none,
      makeInit c (sptFromAList code) oracle {source with clock := fuel}) = (result, post))
    (notError : result ≠ some .error) :
    ∃ final, StackSemEvaluate.evaluate (.call none (.inl entry) none,
      {source with clock := fuel}) = (result, final) ∧ final.ffi = post.ffi ∧
      stackExecutionCost (fun p _ => price p) (.call none (.inl entry) none) {source with clock := fuel} ≤
        stackExecutionCost (fun p _ => price p) (.call none (.inl entry) none)
          (makeInit c (sptFromAList code) oracle {source with clock := fuel}) := by
  have totalEq : InitMake.makeInitAny generateGc maxHeap bitmaps dataSpace (oracleMap ∘ oracle)
      jump bounds pointer (sptFromAList (compile c code)) base = source := by
    unfold InitMake.makeInitAny
    rw [selected]
  have stack := InitAny.makeInitAnyUseStack generateGc maxHeap bitmaps dataSpace
    (oracleMap ∘ oracle) jump bounds pointer (sptFromAList (compile c code)) base
  have store := InitAny.makeInitAnyUseStore generateGc maxHeap bitmaps dataSpace
    (oracleMap ∘ oracle) jump bounds pointer (sptFromAList (compile c code)) base
  have alloc := InitAny.makeInitAnyUseAlloc generateGc maxHeap bitmaps dataSpace
    (oracleMap ∘ oracle) jump bounds pointer (sptFromAList (compile c code)) base
  have codeEq := InitAny.makeInitAnyCode generateGc maxHeap bitmaps dataSpace
    (oracleMap ∘ oracle) jump bounds pointer (sptFromAList (compile c code)) base
  have oracleEq := InitAny.makeInitAnyCompileOracle generateGc maxHeap bitmaps dataSpace
    (oracleMap ∘ oracle) jump bounds pointer (sptFromAList (compile c code)) base
  have stackBound := InitAny.makeInitAnyStackLimit generateGc maxHeap bitmaps dataSpace
    (oracleMap ∘ oracle) jump bounds pointer (sptFromAList (compile c code)) base
  rw [totalEq] at stack store alloc codeEq oracleEq stackBound
  obtain ⟨normalPost, sourceEq, prop⟩ := InitAny.makeInitOpt_eq_some selected
  have buf : BufBound source := by
    subst sourceEq
    rcases prop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hdb, _, _, _, hbl, _⟩
    simp only [InitReduce.initReduce] at hbl hdb ⊢
    simp only [BufBound, List.length_nil, Nat.add_zero]
    omega
  obtain ⟨regs1, evaluated, _, cost⟩ := initialized_entry_executed_cost price code oracle
    {source with clock := fuel} post c entry result codeArgs oracleArgs
    stack store alloc codeEq oracleEq buf stackBound codeFree oracleFree run notError
  exact ⟨Res source.gcFun source.compile c post regs1, evaluated, rfl, cost⟩


#print axioms selected_entry_executed_cost
end InitECandidate.Runtime.StackAlloc
