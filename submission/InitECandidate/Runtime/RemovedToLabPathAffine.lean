import InitECandidate.Runtime.InitializedStackAffine
import InitECandidate.Runtime.StackRemoveAffineEntryBudget

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Concrete clock composition through removal, naming and label lowering.
The input evaluation is still at the allocated StackSem stage. -/
theorem before_remove_halt_affine_path {width : Nat} [NeZero width] {C F : Type}
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
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      {source with clock := fuel}) = (some (.halt (.word value)), post)) :
    ∃ removedClock clocks final,
      removedClock ≤ fuel + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := fuel} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (if value = 0 then .halt .success else .halt .resourceLimitHit, final) ∧ final.ffi = post.ffi := by
  obtain ⟨removedClock, removedPost, removedBound, removedRun, removedFfi⟩ :=
    InitECandidate.Runtime.StackRemove.discharge_entry_affine_bounded stackConf.jump offset
      (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
      (coracle1 oracle) (code1 dataConf code)
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) bitmaps dataSp
      ⟨dischargeThese_s2 initialized, propagateThese_s2 initialized⟩
      source post fuel (some (.halt (.word value))) selected run (by simp)
  have clockInitialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code
      {target with clock := removedClock} saveRegs dataSp oracle := initialized
  obtain ⟨clocks, final, bound, evaluated, ffi⟩ :=
    before_names_halt_affine stackConf dataConf maxHeap sp offset bitmaps code
      {target with clock := removedClock} saveRegs dataSp oracle removedPost value clockInitialized limit (bounded removedClock) removedRun
  exact ⟨removedClock, clocks, final, removedBound, bound, evaluated, ffi.trans removedFfi⟩

theorem before_remove_ffi_affine_path {width : Nat} [NeZero width] {C F : Type}
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
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      {source with clock := fuel}) = (some (.finalFFI event), post)) :
    ∃ removedClock clocks final,
      removedClock ≤ fuel + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := fuel} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (.halt (.ffiOutcome event), final) ∧ final.ffi = post.ffi := by
  obtain ⟨removedClock, removedPost, removedBound, removedRun, removedFfi⟩ :=
    InitECandidate.Runtime.StackRemove.discharge_entry_affine_bounded stackConf.jump offset
      (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
      (coracle1 oracle) (code1 dataConf code)
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) bitmaps dataSp
      ⟨dischargeThese_s2 initialized, propagateThese_s2 initialized⟩
      source post fuel (some (.finalFFI event)) selected run (by simp)
  have clockInitialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code
      {target with clock := removedClock} saveRegs dataSp oracle := initialized
  obtain ⟨clocks, final, bound, evaluated, ffi⟩ :=
    before_names_ffi_affine stackConf dataConf maxHeap sp offset bitmaps code
      {target with clock := removedClock} saveRegs dataSp oracle removedPost event clockInitialized limit (bounded removedClock) removedRun
  exact ⟨removedClock, clocks, final, removedBound, bound, evaluated, ffi.trans removedFfi⟩

theorem before_remove_return_affine_path {width : Nat} [NeZero width] {C F : Type}
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
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : StackSemEvaluate.evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      {source with clock := fuel}) = (some (.result (.loc 1 0)), post)) :
    ∃ removedClock clocks final,
      removedClock ≤ fuel + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := fuel} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate { target with clock := removedClock - 1 + clocks } =
        (.halt .success, final) ∧ final.ffi = post.ffi := by
  obtain ⟨removedClock, removedPost, removedBound, removedRun, removedFfi⟩ :=
    InitECandidate.Runtime.StackRemove.discharge_entry_affine_bounded stackConf.jump offset
      (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
      (coracle1 oracle) (code1 dataConf code)
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) bitmaps dataSp
      ⟨dischargeThese_s2 initialized, propagateThese_s2 initialized⟩
      source post fuel (some (.result (.loc 1 0))) selected run (by simp)
  have clockInitialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code
      {target with clock := removedClock} saveRegs dataSp oracle := initialized
  obtain ⟨clocks, final, bound, evaluated, ffi⟩ :=
    before_names_return_affine stackConf dataConf maxHeap sp offset bitmaps code
      {target with clock := removedClock} saveRegs dataSp oracle removedPost clockInitialized limit (bounded removedClock) removedRun
  exact ⟨removedClock, clocks, final, removedBound, bound, evaluated, ffi.trans removedFfi⟩


#print axioms before_remove_return_affine_path
#print axioms before_remove_halt_affine_path
#print axioms before_remove_ffi_affine_path
end InitECandidate.Runtime.StackToLab
