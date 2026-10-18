import InitECandidate.Runtime.WordInitializedBudget
import InitECandidate.Runtime.RawToLabPathAffine
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Resource rejection survives every stage from WordToStack through labels,
with explicit composed clock bounds and the original resource trace alternative. -/
theorem word_resource_to_lab_affine_path {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) (fuel : Nat)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (selected : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source)
    (codeFree : StackAlloc.allocationFreeCode (StackRawCall.compile code) = true)
    (oracleFree : ∀ n, StackAlloc.allocationFreeCode (oracle n).2.1 = true)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (k : Nat)
    (wordSource : WordSemStateFiniteExact width (Nat × C) F)
    (wordPost : WordSemStateFiniteExact width (Nat × C) F)
    (related : Flapjack.WordToStackProofs.stateRel ac k 0 0 wordSource
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) [] 0)
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {wordSource with clock := fuel} = (some .notEnoughSpace, wordPost)) :
    ∃ wordClock rawClock removedClock clocks final,
      wordClock ≤ fuel + WordToStack.wordWork
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none) {wordSource with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate {target with clock := removedClock - 1 + clocks} = (.halt .resourceLimitHit, final) ∧
      (final.ffi = wordPost.ffi ∨
        (List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
         wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc, res, wp, wb, wr, oneNe, twoNe, outcomes⟩ :=
    WordToStack.entrySimulation_with_resource_words_bounded ac k wordSource
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source)
      [] BvlToBvi.initGlobalsLocation fuel (some .notEnoughSpace) wordPost related run (by simp)
  rcases outcomes with ⟨same, ffi, clock⟩ | ⟨different, halt, eventPrefix, overflow⟩
  · have resultEq : res = some (.halt (.word 1)) := by
      simpa only [Option.map_some, Flapjack.WordToStackProofs.CompCorrect.compileResult] using same.symm
    rw [resultEq] at wr
    obtain ⟨rc, mc, lc, final, rb, mb, lb, evaluated, finalFfi⟩ :=
      before_raw_halt_affine_path stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
        dataSp oracle source wc wp 1 initialized selected codeFree oracleFree limit bounded wr
    refine ⟨wc, rc, mc, lc, final, wb, rb, mb, lb, ?_, Or.inl (finalFfi.trans ffi.symm)⟩
    simpa only [if_neg oneNe] using evaluated
  · rw [halt] at wr
    obtain ⟨rc, mc, lc, final, rb, mb, lb, evaluated, finalFfi⟩ :=
      before_raw_halt_affine_path stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
        dataSp oracle source wc wp 2 initialized selected codeFree oracleFree limit bounded wr
    refine ⟨wc, rc, mc, lc, final, wb, rb, mb, lb, ?_, Or.inr ⟨?_, overflow⟩⟩
    · simpa only [if_neg twoNe] using evaluated
    · rw [finalFfi]
      exact eventPrefix

/-- A final FFI outcome transfers through the full stack pipeline, or the
original WordToStack resource alternative produces a resource-limit outcome. -/
theorem word_ffi_to_lab_affine_path {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) (fuel : Nat)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (selected : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source)
    (codeFree : StackAlloc.allocationFreeCode (StackRawCall.compile code) = true)
    (oracleFree : ∀ n, StackAlloc.allocationFreeCode (oracle n).2.1 = true)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (k : Nat)
    (wordSource : WordSemStateFiniteExact width (Nat × C) F)
    (wordPost : WordSemStateFiniteExact width (Nat × C) F)
    (related : Flapjack.WordToStackProofs.stateRel ac k 0 0 wordSource
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) [] 0)
    (event : HolFinalEvent)
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {wordSource with clock := fuel} = (some (.finalFfi event), wordPost)) :
    ∃ wordClock rawClock removedClock clocks final outcome,
      wordClock ≤ fuel + WordToStack.wordWork
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none) {wordSource with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate {target with clock := removedClock - 1 + clocks} = (.halt outcome, final) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
         wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc, res, wp, wb, wr, oneNe, twoNe, outcomes⟩ :=
    WordToStack.entrySimulation_with_resource_words_bounded ac k wordSource
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source)
      [] BvlToBvi.initGlobalsLocation fuel (some (.finalFfi event)) wordPost related run (by simp)
  rcases outcomes with ⟨same, ffi, clock⟩ | ⟨different, halt, eventPrefix, overflow⟩
  · have resultEq : res = some (.finalFFI event) := by
      simpa only [Option.map_some, Flapjack.WordToStackProofs.CompCorrect.compileResult] using same.symm
    rw [resultEq] at wr
    obtain ⟨rc, mc, lc, final, rb, mb, lb, evaluated, finalFfi⟩ :=
      before_raw_ffi_affine_path stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
        dataSp oracle source wc wp event initialized selected codeFree oracleFree limit bounded wr
    exact ⟨wc, rc, mc, lc, final, .ffiOutcome event, wb, rb, mb, lb, evaluated,
      Or.inl ⟨rfl, finalFfi.trans ffi.symm⟩⟩
  · rw [halt] at wr
    obtain ⟨rc, mc, lc, final, rb, mb, lb, evaluated, finalFfi⟩ :=
      before_raw_halt_affine_path stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
        dataSp oracle source wc wp 2 initialized selected codeFree oracleFree limit bounded wr
    refine ⟨wc, rc, mc, lc, final, .resourceLimitHit, wb, rb, mb, lb, ?_, Or.inr ⟨rfl, ?_, overflow⟩⟩
    · simpa only [if_neg twoNe] using evaluated
    · rw [finalFfi]
      exact eventPrefix

/-- Successful Word entry return transfers through the full stack pipeline,
retaining the bounded resource-limit alternative. -/
theorem word_return_to_lab_affine_path {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) (fuel : Nat)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (selected : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source)
    (codeFree : StackAlloc.allocationFreeCode (StackRawCall.compile code) = true)
    (oracleFree : ∀ n, StackAlloc.allocationFreeCode (oracle n).2.1 = true)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (k : Nat)
    (wordSource : WordSemStateFiniteExact width (Nat × C) F)
    (wordPost : WordSemStateFiniteExact width (Nat × C) F)
    (related : Flapjack.WordToStackProofs.stateRel ac k 0 0 wordSource
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) [] 0)
    (values : List (WordLocW width))
    (limit : Nat)
    (bounded : ∀ fuel, CodeSizeState limit (s3 stackConf dataConf maxHeap sp offset code
      {target with clock := fuel} saveRegs oracle))
    (run : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {wordSource with clock := fuel} = (some (.result (.loc 1 0) values), wordPost)) :
    ∃ wordClock rawClock removedClock clocks final outcome,
      wordClock ≤ fuel + WordToStack.wordWork
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none) {wordSource with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeAffineWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * limit + 2) * removedClock + 4 * limit ∧
      evaluate {target with clock := removedClock - 1 + clocks} = (.halt outcome, final) ∧
      ((outcome = .success ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
         wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc, res, wp, wb, wr, oneNe, twoNe, outcomes⟩ :=
    WordToStack.entrySimulation_with_resource_words_bounded ac k wordSource
      (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source)
      [] BvlToBvi.initGlobalsLocation fuel (some (.result (.loc 1 0) values)) wordPost related run (by simp)
  rcases outcomes with ⟨same, ffi, clock⟩ | ⟨different, halt, eventPrefix, overflow⟩
  · have resultEq : res = some (.result (.loc 1 0)) := by
      simpa only [Option.map_some, Flapjack.WordToStackProofs.CompCorrect.compileResult] using same.symm
    rw [resultEq] at wr
    obtain ⟨rc, mc, lc, final, rb, mb, lb, evaluated, finalFfi⟩ :=
      before_raw_return_affine_path stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
        dataSp oracle source wc wp initialized selected codeFree oracleFree limit bounded wr
    exact ⟨wc, rc, mc, lc, final, .success, wb, rb, mb, lb, evaluated,
      Or.inl ⟨rfl, finalFfi.trans ffi.symm⟩⟩
  · rw [halt] at wr
    obtain ⟨rc, mc, lc, final, rb, mb, lb, evaluated, finalFfi⟩ :=
      before_raw_halt_affine_path stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
        dataSp oracle source wc wp 2 initialized selected codeFree oracleFree limit bounded wr
    refine ⟨wc, rc, mc, lc, final, .resourceLimitHit, wb, rb, mb, lb, ?_, Or.inr ⟨rfl, ?_, overflow⟩⟩
    · simpa only [if_neg twoNe] using evaluated
    · rw [finalFfi]
      exact eventPrefix

#print axioms word_return_to_lab_affine_path

#print axioms word_ffi_to_lab_affine_path

#print axioms word_resource_to_lab_affine_path
end InitECandidate.Runtime.StackToLab
