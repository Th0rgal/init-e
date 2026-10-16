import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit

/-- Initialization assumptions prove that removal selects a real state and
that the full pre-RawCall initializer is allocation's initializer on that state. -/
theorem selected_initialization_exists {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle) :
    ∃ source, StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source ∧
      fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle =
        (Flapjack.Compiler.Backend.StackAlloc.makeInit dataConf (sptFromAList code) oracle source,
         some source) := by
  let result := fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle
  have nonempty := (fullMakeInitSemantics (s := result.1) (opt := result.2) ⟨rfl, initialized⟩).1
  obtain ⟨source, selected⟩ := Option.ne_none_iff_exists'.mp nonempty
  have selection : StackRemove.Proofs.InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind)
      maxHeap bitmaps dataSp (coracle1 oracle) stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some source := selected
  refine ⟨source, selection, ?_⟩
  rw [fullMakeInit_eq]
  simp only [selection, StackRemove.Proofs.InitMake.makeInitAny]

#print axioms selected_initialization_exists
end InitECandidate.Runtime.StackToLab
