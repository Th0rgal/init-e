import InitECandidate.Runtime.FullAllocationBudget
import InitECandidate.Runtime.RemovedToLabBudget

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Concrete clock composition from the unallocated Raw entry through allocation,
removal, naming and label lowering, preserving the actual terminal and FFI. -/
theorem before_alloc_halt_bounded {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) (fuel : Nat)
    (post : StackSemStateFiniteExact width C F) (value : BitVec width)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (selected : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source)
    (codeFree : StackAlloc.allocationFreeCode (StackRawCall.compile code) = true)
    (oracleFree : ∀ n, StackAlloc.allocationFreeCode (oracle n).2.1 = true)
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
        (sptFromAList (StackRawCall.compile code)) oracle {source with clock := fuel}) = (some (.halt (.word value)), post)) :
    ∃ removedClock clocks final,
      removedClock ≤ fuel + InitECandidate.Runtime.StackRemove.removeWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := fuel} + 1 ∧
      clocks ≤ entryWork 0 (s3 stackConf dataConf maxHeap sp offset code
        {target with clock := removedClock} saveRegs oracle) ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (if value = 0 then .halt .success else .halt .resourceLimitHit, final) ∧ final.ffi = post.ffi := by
  obtain ⟨allocatedPost, allocatedRun, allocatedFfi⟩ := before_alloc_entry_same_clock
    stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle
    source post fuel (some (.halt (.word value))) initialized selected codeFree oracleFree run (by simp)
  obtain ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi⟩ :=
    before_remove_halt_bounded stackConf dataConf maxHeap sp offset bitmaps code target
      saveRegs dataSp oracle source fuel allocatedPost value initialized selected allocatedRun
  exact ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi.trans allocatedFfi⟩

/-- Concrete clock composition from the unallocated Raw entry through allocation,
removal, naming and label lowering, preserving the actual terminal and FFI. -/
theorem before_alloc_ffi_bounded {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) (fuel : Nat)
    (post : StackSemStateFiniteExact width C F) (event : HolFinalEvent)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (selected : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source)
    (codeFree : StackAlloc.allocationFreeCode (StackRawCall.compile code) = true)
    (oracleFree : ∀ n, StackAlloc.allocationFreeCode (oracle n).2.1 = true)
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
        (sptFromAList (StackRawCall.compile code)) oracle {source with clock := fuel}) = (some (.finalFFI event), post)) :
    ∃ removedClock clocks final,
      removedClock ≤ fuel + InitECandidate.Runtime.StackRemove.removeWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := fuel} + 1 ∧
      clocks ≤ entryWork 0 (s3 stackConf dataConf maxHeap sp offset code
        {target with clock := removedClock} saveRegs oracle) ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (.halt (.ffiOutcome event), final) ∧ final.ffi = post.ffi := by
  obtain ⟨allocatedPost, allocatedRun, allocatedFfi⟩ := before_alloc_entry_same_clock
    stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle
    source post fuel (some (.finalFFI event)) initialized selected codeFree oracleFree run (by simp)
  obtain ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi⟩ :=
    before_remove_ffi_bounded stackConf dataConf maxHeap sp offset bitmaps code target
      saveRegs dataSp oracle source fuel allocatedPost event initialized selected allocatedRun
  exact ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi.trans allocatedFfi⟩

/-- Concrete clock composition from the unallocated Raw entry through allocation,
removal, naming and label lowering, preserving the actual terminal and FFI. -/
theorem before_alloc_return_bounded {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) (fuel : Nat)
    (post : StackSemStateFiniteExact width C F)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (selected : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source)
    (codeFree : StackAlloc.allocationFreeCode (StackRawCall.compile code) = true)
    (oracleFree : ∀ n, StackAlloc.allocationFreeCode (oracle n).2.1 = true)
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
        (sptFromAList (StackRawCall.compile code)) oracle {source with clock := fuel}) = (some (.result (.loc 1 0)), post)) :
    ∃ removedClock clocks final,
      removedClock ≤ fuel + InitECandidate.Runtime.StackRemove.removeWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := fuel} + 1 ∧
      clocks ≤ entryWork 0 (s3 stackConf dataConf maxHeap sp offset code
        {target with clock := removedClock} saveRegs oracle) ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (.halt .success, final) ∧ final.ffi = post.ffi := by
  obtain ⟨allocatedPost, allocatedRun, allocatedFfi⟩ := before_alloc_entry_same_clock
    stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle
    source post fuel (some (.result (.loc 1 0))) initialized selected codeFree oracleFree run (by simp)
  obtain ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi⟩ :=
    before_remove_return_bounded stackConf dataConf maxHeap sp offset bitmaps code target
      saveRegs dataSp oracle source fuel allocatedPost initialized selected allocatedRun
  exact ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi.trans allocatedFfi⟩

#print axioms before_alloc_halt_bounded
#print axioms before_alloc_ffi_bounded
#print axioms before_alloc_return_bounded
end InitECandidate.Runtime.StackToLab
