import InitECandidate.Runtime.StackAllocSelectedBudget
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Instantiate allocation lowering at the actual selected source of the full
compiler initializer. Original GoodCode discharges allocation-call premises;
only the additional syntax certificates remain explicit. -/
theorem before_alloc_entry_same_clock {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source post : StackSemStateFiniteExact width C F) (fuel : Nat)
    (result : Option (StackSemResult width))
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (selected : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source)
    (codeFree : StackAlloc.allocationFreeCode (StackRawCall.compile code) = true)
    (oracleFree : ∀ n, StackAlloc.allocationFreeCode (oracle n).2.1 = true)
    (run : StackSemEvaluate.evaluate (.call none (.inl BvlToBvi.initGlobalsLocation) none,
      Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
        (sptFromAList (StackRawCall.compile code)) oracle {source with clock := fuel}) = (result, post))
    (notError : result ≠ some .error) :
    ∃ final, StackSemEvaluate.evaluate (.call none (.inl BvlToBvi.initGlobalsLocation) none,
      {source with clock := fuel}) = (result, final) ∧ final.ffi = post.ffi := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, good, goodOracle, -, -, -, -, -, -, -, -⟩ := id initialized
  refine StackAlloc.selected_entry_same_clock dataConf (StackRawCall.compile code) oracle
    (StackToLab.isGenGc dataConf.gcKind) maxHeap dataSp sp BvlToBvi.initGlobalsLocation fuel
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

#print axioms before_alloc_entry_same_clock
end InitECandidate.Runtime.StackToLab
