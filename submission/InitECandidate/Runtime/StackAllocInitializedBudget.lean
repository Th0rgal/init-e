import InitECandidate.Runtime.StackAllocZeroCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.MakeInit

namespace InitECandidate.Runtime.StackAlloc
open Flapjack Flapjack.Compiler.Backend Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackAlloc.ProgCompSupport

/-- The pinned compiler's initialized target is exactly the simulation override
of its source initializer. No additional clock or target-run hypothesis occurs. -/
theorem res_makeInit_eq {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s : StackSemStateFiniteExact width C F) (c : DataToWord.Config)
    (stack : s.useStack = true) (store : s.useStore = true) (alloc : s.useAlloc ≠ true)
    (codeEq : s.code = sptFromAList (compile c code))
    (oracleEq : s.compileOracle = oracleMap ∘ oracle) :
    Res s.gcFun s.compile c (makeInit c (sptFromAList code) oracle s) s.regs = s := by
  have normalized : sptFromAList (compile c (sptToAList (sptFromAList code))) = s.code := by
    rw [codeEq]
    refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
    rw [sptLookup_compile, sptLookup_compile,
      sptAListLookup_sptToAList, sptLookup_sptFromAList]
  have allocFalse : s.useAlloc = false := by cases h : s.useAlloc <;> simp_all
  cases s
  simp only [Res, makeInit] at normalized oracleEq stack store allocFalse ⊢
  subst stack store allocFalse
  rw [normalized, oracleEq]

/-- Quantitative initialized allocation lowering for certified code: the actual
entry call runs in the target at exactly the source initializer's clock. -/
theorem initialized_entry_same_clock {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s t : StackSemStateFiniteExact width C F) (c : DataToWord.Config) (entry : Nat)
    (result : Option (StackSemResult width))
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
      (result, Res s.gcFun s.compile c t regs1) ∧ Post result t regs1 := by
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
  obtain ⟨regs1, targetRun, post⟩ := Zero.allocationFree_same_clock s.gcFun s.compile
    (.call none (.inl entry) none) source t result c s.regs
    (by simp [allocationFree]) free run notError (by simp [StackProps.allocArg]) pre
  refine ⟨regs1, ?_, post⟩
  rwa [res_makeInit_eq code oracle s c stack store alloc codeEq oracleEq] at targetRun

#print axioms initialized_entry_same_clock
end InitECandidate.Runtime.StackAlloc
