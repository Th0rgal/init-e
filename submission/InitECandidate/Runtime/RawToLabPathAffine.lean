import InitECandidate.Runtime.RawCallEntryBudget
import InitECandidate.Runtime.AllocatedToLabPathAffine
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Concrete full initialization composition from before RawCall to labels,
with a uniform factor-two RawCall fuel bound and exact terminal/FFI. -/
theorem before_raw_halt_affine_path {width : Nat} [NeZero width] {C F : Type}
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
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
        (sptFromAList code) oracle {source with clock := fuel}) = (some (.halt (.word value)), post)) :
    ∃ rawClock removedClock clocks final, rawClock ≤ 2 * fuel ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (if value = 0 then .halt .success else .halt .resourceLimitHit, final) ∧ final.ffi = post.ffi := by
  have distinct : (code.map Prod.fst).Nodup := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, good, -, -, -, -, -, -, -, -, -⟩ := id initialized
    exact good.1
  obtain ⟨rawClock, rawPost, rawBound, rawEvaluated, rawFfi⟩ :=
    StackRawCall.entrySimulation_twice code
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source)
      BvlToBvi.initGlobalsLocation fuel (some (.halt (.word value))) post distinct rfl run (by simp)
  have rawRun : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
          (sptFromAList (StackRawCall.compile code)) oracle {source with clock := rawClock}) =
      (some (.halt (.word value)), rawPost) := by
    simpa only [Flapjack.Compiler.Backend.StackAlloc.makeInit] using rawEvaluated
  obtain ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi⟩ :=
    before_alloc_halt_affine_path stackConf dataConf maxHeap sp offset bitmaps code target
      saveRegs dataSp oracle source rawClock rawPost value initialized selected codeFree oracleFree limit bounded rawRun
  exact ⟨rawClock, removedClock, clocks, final, rawBound, removedBound, labelBound,
    evaluated, ffi.trans rawFfi⟩

/-- Concrete full initialization composition from before RawCall to labels,
with a uniform factor-two RawCall fuel bound and exact terminal/FFI. -/
theorem before_raw_ffi_affine_path {width : Nat} [NeZero width] {C F : Type}
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
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
        (sptFromAList code) oracle {source with clock := fuel}) = (some (.finalFFI event), post)) :
    ∃ rawClock removedClock clocks final, rawClock ≤ 2 * fuel ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (.halt (.ffiOutcome event), final) ∧ final.ffi = post.ffi := by
  have distinct : (code.map Prod.fst).Nodup := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, good, -, -, -, -, -, -, -, -, -⟩ := id initialized
    exact good.1
  obtain ⟨rawClock, rawPost, rawBound, rawEvaluated, rawFfi⟩ :=
    StackRawCall.entrySimulation_twice code
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source)
      BvlToBvi.initGlobalsLocation fuel (some (.finalFFI event)) post distinct rfl run (by simp)
  have rawRun : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
          (sptFromAList (StackRawCall.compile code)) oracle {source with clock := rawClock}) =
      (some (.finalFFI event), rawPost) := by
    simpa only [Flapjack.Compiler.Backend.StackAlloc.makeInit] using rawEvaluated
  obtain ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi⟩ :=
    before_alloc_ffi_affine_path stackConf dataConf maxHeap sp offset bitmaps code target
      saveRegs dataSp oracle source rawClock rawPost event initialized selected codeFree oracleFree limit bounded rawRun
  exact ⟨rawClock, removedClock, clocks, final, rawBound, removedBound, labelBound,
    evaluated, ffi.trans rawFfi⟩

/-- Concrete full initialization composition from before RawCall to labels,
with a uniform factor-two RawCall fuel bound and exact terminal/FFI. -/
theorem before_raw_return_affine_path {width : Nat} [NeZero width] {C F : Type}
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
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
        (sptFromAList code) oracle {source with clock := fuel}) = (some (.result (.loc 1 0)), post)) :
    ∃ rawClock removedClock clocks final, rawClock ≤ 2 * fuel ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (.halt .success, final) ∧ final.ffi = post.ffi := by
  have distinct : (code.map Prod.fst).Nodup := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, good, -, -, -, -, -, -, -, -, -⟩ := id initialized
    exact good.1
  obtain ⟨rawClock, rawPost, rawBound, rawEvaluated, rawFfi⟩ :=
    StackRawCall.entrySimulation_twice code
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source)
      BvlToBvi.initGlobalsLocation fuel (some (.result (.loc 1 0))) post distinct rfl run (by simp)
  have rawRun : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf
          (sptFromAList (StackRawCall.compile code)) oracle {source with clock := rawClock}) =
      (some (.result (.loc 1 0)), rawPost) := by
    simpa only [Flapjack.Compiler.Backend.StackAlloc.makeInit] using rawEvaluated
  obtain ⟨removedClock, clocks, final, removedBound, labelBound, evaluated, ffi⟩ :=
    before_alloc_return_affine_path stackConf dataConf maxHeap sp offset bitmaps code target
      saveRegs dataSp oracle source rawClock rawPost initialized selected codeFree oracleFree limit bounded rawRun
  exact ⟨rawClock, removedClock, clocks, final, rawBound, removedBound, labelBound,
    evaluated, ffi.trans rawFfi⟩

#print axioms before_raw_halt_affine_path
#print axioms before_raw_ffi_affine_path
#print axioms before_raw_return_affine_path
end InitECandidate.Runtime.StackToLab
