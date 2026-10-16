import InitECandidate.Runtime.StackAllocInitializedBudget
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitAny

namespace InitECandidate.Runtime.StackAlloc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- A successful stack-removal initializer supplies the actual allocation-stage
state and all of its machine bounds. Certified allocation lowering transmits
entry execution to that selected state with exactly the supplied fuel. -/
theorem selected_entry_same_clock {width : Nat} [NeZero width] {C F : Type}
    (c : DataToWord.Config) (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (generateGc : Bool) (maxHeap dataSpace pointer entry fuel : Nat)
    (bitmaps : List (BitVec width)) (jump : Bool) (bounds : BitVec width × BitVec width)
    (base source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
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
      {source with clock := fuel}) = (result, final) ∧ final.ffi = post.ffi := by
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
  obtain ⟨regs1, evaluated, _⟩ := initialized_entry_same_clock code oracle
    {source with clock := fuel} post c entry result codeArgs oracleArgs
    stack store alloc codeEq oracleEq buf stackBound codeFree oracleFree run notError
  exact ⟨Res source.gcFun source.compile c post regs1, evaluated, rfl⟩

#print axioms selected_entry_same_clock
end InitECandidate.Runtime.StackAlloc
