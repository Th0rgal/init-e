import InitECandidate.Runtime.PipelineWordInitialization
import InitECandidate.Runtime.SelectedFullInitialization
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyWordToStack
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.Pancake.PanLang

open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
/-- Stack initialization assumptions and actual compiler results select the real
source state and derive the full Word initialization premise bundle. -/
theorem selected_word_initialization {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (word : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (frames : List Nat)
    (stack : List (Nat × StackLang.HolProg width)) (cfg : C)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wordRun : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, word))
    (stackRun : WordToStack.Native.compileNative ac false word = (bitmaps, wconf, frames, stack))
    (assumptions : Assumptions sc dc maxHeap sp offset bitmaps stack lab saveRegs dataSp
      (fun _ => (cfg, [], []))) :
    ∃ selected,
      StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dc.gcKind)
        maxHeap bitmaps dataSp (coracle1 (fun _ => (cfg, [], []))) sc.jump offset sp
        (sptFromAList (code1 dc stack))
        (s2 sc dc maxHeap sp offset stack lab saveRegs (fun _ => (cfg, [], []))) = some selected ∧
      InitializationPremises ac word
        (Flapjack.Compiler.Backend.StackAlloc.makeInit dc (sptFromAList stack)
          (fun _ => (cfg, [], [])) selected)
        (ac.regCount - (5 + ac.avoidRegs.length))
        (fun _ => ((bitmaps.length, cfg), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width))))) := by
  obtain ⟨selected, selection, fullRun⟩ :=
    InitECandidate.Runtime.StackToLab.selected_initialization_exists sc dc maxHeap sp offset
      bitmaps stack lab saveRegs dataSp (fun _ => (cfg, [], [])) assumptions
  refine ⟨selected, selection, ?_⟩
  exact pipeline_word_initialization ac wc panCode col word bitmaps wconf frames stack cfg sc dc
    maxHeap sp offset lab saveRegs dataSp _ selected dimension registers isa wordRun stackRun fullRun

#print axioms selected_word_initialization
end InitECandidate.Runtime.WordToStack
