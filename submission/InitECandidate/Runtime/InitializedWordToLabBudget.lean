import InitECandidate.Runtime.WordToLabBudget
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Derives the full WordToStack relation from actual compiler initialization. -/
theorem initialized_word_resource_to_lab_bounded {width : Nat} [NeZero width] {C F : Type}
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
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wordOracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wordPost : WordSemStateFiniteExact width (Nat × C) F)
    (wordInitialized : WordToStack.InitializationPremises ac wordCode (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) k wordOracle)
    (run : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {(Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) with clock := fuel} = (some .notEnoughSpace, wordPost)) :
    ∃ wordClock rawClock removedClock clocks final,
      wordClock ≤ fuel + WordToStack.wordWork
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none) {(Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ entryWork 0 (s3 stackConf dataConf maxHeap sp offset code
        {target with clock := removedClock} saveRegs oracle) ∧
      evaluate {target with clock := removedClock - 1 + clocks} = (.halt .resourceLimitHit, final) ∧
      (final.ffi = wordPost.ffi ∨
        (List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
         wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  exact word_resource_to_lab_bounded stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
    dataSp oracle source fuel initialized selected codeFree oracleFree ac k
    (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) wordPost
    (WordToStack.initialized_relation ac wordCode (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) k wordOracle wordInitialized) run

#print axioms initialized_word_resource_to_lab_bounded

/-- Derives the full WordToStack relation from actual compiler initialization. -/
theorem initialized_word_ffi_to_lab_bounded {width : Nat} [NeZero width] {C F : Type}
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
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wordOracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wordPost : WordSemStateFiniteExact width (Nat × C) F)
    (wordInitialized : WordToStack.InitializationPremises ac wordCode (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) k wordOracle)
    (event : HolFinalEvent)
    (run : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {(Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) with clock := fuel} = (some (.finalFfi event), wordPost)) :
    ∃ wordClock rawClock removedClock clocks final outcome,
      wordClock ≤ fuel + WordToStack.wordWork
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none) {(Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ entryWork 0 (s3 stackConf dataConf maxHeap sp offset code
        {target with clock := removedClock} saveRegs oracle) ∧
      evaluate {target with clock := removedClock - 1 + clocks} = (.halt outcome, final) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
         wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  exact word_ffi_to_lab_bounded stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
    dataSp oracle source fuel initialized selected codeFree oracleFree ac k
    (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) wordPost
    (WordToStack.initialized_relation ac wordCode (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) k wordOracle wordInitialized) event run

#print axioms initialized_word_ffi_to_lab_bounded

/-- Derives the full WordToStack relation from actual compiler initialization. -/
theorem initialized_word_return_to_lab_bounded {width : Nat} [NeZero width] {C F : Type}
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
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wordOracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wordPost : WordSemStateFiniteExact width (Nat × C) F)
    (wordInitialized : WordToStack.InitializationPremises ac wordCode (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) k wordOracle)
    (values : List (WordLocW width))
    (run : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {(Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) with clock := fuel} = (some (.result (.loc 1 0) values), wordPost)) :
    ∃ wordClock rawClock removedClock clocks final outcome,
      wordClock ≤ fuel + WordToStack.wordWork
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none) {(Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + InitECandidate.Runtime.StackRemove.removeWork
        (.call none (.inl BvlToBvi.initGlobalsLocation) none) {source with clock := rawClock} + 1 ∧
      clocks ≤ entryWork 0 (s3 stackConf dataConf maxHeap sp offset code
        {target with clock := removedClock} saveRegs oracle) ∧
      evaluate {target with clock := removedClock - 1 + clocks} = (.halt outcome, final) ∧
      ((outcome = .success ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
         wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  exact word_return_to_lab_bounded stackConf dataConf maxHeap sp offset bitmaps code target saveRegs
    dataSp oracle source fuel initialized selected codeFree oracleFree ac k
    (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) (sptFromAList wordCode) wordOracle) wordPost
    (WordToStack.initialized_relation ac wordCode (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source) k wordOracle wordInitialized) values run

#print axioms initialized_word_return_to_lab_bounded
end InitECandidate.Runtime.StackToLab
