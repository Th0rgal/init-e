import InitECandidate.Runtime.WordInitializedBudget
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyWordToStack
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.Pancake.PanLang

/-- Derive every WordToStack entry premise from actual pass results and a
successful full stack initializer. No Word relation or source evaluation is assumed. -/
theorem pipeline_word_initialization {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (word : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (frames : List Nat)
    (stack : List (Nat × StackLang.HolProg width)) (cfg : C)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (sst selected : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wordRun : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, word))
    (stackRun : WordToStack.Native.compileNative ac false word = (bitmaps, wconf, frames, stack))
    (initialized : StackToLab.Proofs.FullMakeInit.fullMakeInit sc dc maxHeap sp offset bitmaps
      stack lab saveRegs dataSp (fun _ => (cfg, [], [])) = (sst, some selected)) :
    InitializationPremises ac word sst (ac.regCount - (5 + ac.avoidRegs.length))
      (fun _ => ((bitmaps.length, cfg), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width))))) := by
  obtain ⟨bitmapEq, codeEq⟩ := fullMakeInit_bitmaps_code sc dc maxHeap sp offset bitmaps
    stack lab saveRegs dataSp _ sst selected initialized
  have init := panToTargetInitStateOk ac word bitmaps wconf frames stack cfg sc dc maxHeap sp
    offset lab saveRegs dataSp sst selected dimension registers stackRun initialized
  rw [Nat.add_comm ac.avoidRegs.length 5] at init
  obtain ⟨raiseFree, storeFree⟩ := panToTargetStubLocationsFree wc ac panCode col word isa wordRun
  have conventions := (BackendProof.compileToWordConventions2 wc ac _ col word wordRun
    (fun _ _ => Or.inr isa)).2.2
  refine ⟨?_, rfl, init, raiseFree, storeFree, ?_, ?_⟩
  · rw [stackRun, codeEq]
  · rw [stackRun, bitmapEq]
  · intro entry member
    exact ⟨(conventions entry member).1, (conventions entry member).2.1⟩

#print axioms pipeline_word_initialization
end InitECandidate.Runtime.WordToStack
