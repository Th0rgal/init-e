import InitECandidate.Runtime.StackAllocSelectedExecutedCost
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- The allocation stage on the actual full-compiler initializer, with all
code/oracle allocation-call conditions derived from its original GoodCode
premises. The executed-cost coefficient remains one. -/
theorem before_alloc_entry_executed_cost {C F : Type} (price : HolProg 64 → Nat)
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (target : LabSem.State 64 C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg 64) × List (BitVec 64))
    (source post : StackSemStateFiniteExact 64 C F) (fuel entry : Nat)
    (result : Option (StackSemResult 64))
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (selected : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source)
    (codeFree : StackAlloc.allocationFreeCode (StackRawCall.compile code) = true)
    (oracleFree : ∀ n, StackAlloc.allocationFreeCode (oracle n).2.1 = true)
    (run : StackSemEvaluate.evaluate (.call none (.inl entry) none,
      Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
        (sptFromAList (StackRawCall.compile code)) oracle {source with clock := fuel}) = (result, post))
    (notError : result ≠ some .error) :
    ∃ final, StackSemEvaluate.evaluate (.call none (.inl entry) none,
      {source with clock := fuel}) = (result, final) ∧ final.ffi = post.ffi ∧
      stackExecutionCost (fun p _ => price p) (.call none (.inl entry) none) {source with clock := fuel} ≤
        stackExecutionCost (fun p _ => price p) (.call none (.inl entry) none)
          (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
            (sptFromAList (StackRawCall.compile code)) oracle {source with clock := fuel}) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, good, goodOracle, -, -, -, -, -, -, -, -⟩ := id initialized
  refine StackAlloc.selected_entry_executed_cost price dataConf (StackRawCall.compile code) oracle
    (StackToLab.isGenGc dataConf.gcKind) maxHeap dataSp sp entry fuel
    bitmaps stackConf.jump offset
    (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle)
    source post result ?_ ?_ codeFree oracleFree selected run notError
  · intro key body lookup
    obtain ⟨⟨n0, p0⟩, member, equal⟩ := List.mem_map.mp (sptAListLookup_mem _ _ _ lookup)
    simp only [Prod.mk.injEq] at equal
    obtain ⟨rfl, rfl⟩ := equal
    obtain ⟨stub, args⟩ := good.2.1 _ member
    refine ⟨?_, (StackRawCall.callArgComp _ _).2.mpr args⟩
    simp only [stackNumStubs, gcStubLocation] at stub ⊢
    omega
  · intro n key body member
    obtain ⟨stub, args⟩ := (goodOracle n).2.1 _ member
    refine ⟨?_, args⟩
    simp only [stackNumStubs, gcStubLocation] at stub ⊢
    omega


#print axioms before_alloc_entry_executed_cost
end InitECandidate.Runtime.StackToLab
