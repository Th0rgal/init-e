import InitECandidate.Runtime.BaselineActualJointInitialization
import InitECandidate.Runtime.SelectedWordInitialization
import InitECandidate.Proofs.BackendStages.Bitmaps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

abbrev entrySp : Nat := riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)
abbrev entryHeapLimit : Nat := 2 * DataToWord.maxHeapLimit 64 baselineCompilerConfig.dataConf - 1
noncomputable def entrySaveRegs : Nat → Bool := fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)
abbrev entryStackOracle (cfg : LabToTarget.Config) :
    Nat → LabToTarget.Config × List (Nat × StackLang.HolProg 64) × List (BitVec 64) :=
  fun _ => (cfg, [], [])
abbrev entryWordOracle (cfg : LabToTarget.Config) :
    Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  fun _ => ((InitECandidate.bitmaps.length, cfg), [])
noncomputable def entryStackState (cfg : LabToTarget.Config)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory) :=
  Flapjack.Compiler.Backend.StackAlloc.makeInit baselineCompilerConfig.dataConf
    (sptFromAList BackendStages.Native.stack) (entryStackOracle cfg) source
noncomputable def entryWordState (cfg : LabToTarget.Config)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory) :=
  WordToStack.Native.Initialization.makeInit riscvConfig
    (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) (entryStackState cfg source)
    (sptFromAList BackendStages.Native.programs0) (entryWordOracle cfg)

/-- Concrete, jointly certified entry witnesses for every quantitatively proved
backend stage. Its native bound uses the same label state as stack initialization. -/
structure BaselineRuntimeEntry (input : Guest.InputBlob) where
  cfg : LabToTarget.Config
  asm : AsmState 64
  memory : BitVec 64 → WordLocW 64
  bitmapDomain : BitVec 64 → Bool
  sharedDomain : BitVec 64 → Bool
  source : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory
  memoryAgreement : ∀ a, (sourceInitialState input).memaddrs a →
    memory a = (wlabWlocExact ∘ (sourceInitialState input).memory) a
  sharedAgreement : (sourceInitialState input).shMemaddrs =
    (fun a => sharedDomain a = true ∧ holByteAligned a = true)
  stackAssumptions : Assumptions baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
    entryHeapLimit entrySp riscvConfig.addrOffset InitECandidate.bitmaps BackendStages.Native.stack
    (LabToTarget.baselineLabState input cfg asm memory bitmapDomain sharedDomain)
    entrySaveRegs 0 (entryStackOracle cfg)
  selection : StackRemove.Proofs.InitMake.makeInitOpt
    (StackToLab.isGenGc baselineCompilerConfig.dataConf.gcKind) entryHeapLimit InitECandidate.bitmaps
    0 (coracle1 (entryStackOracle cfg)) baselineCompilerConfig.stackConf.jump riscvConfig.addrOffset
    entrySp (sptFromAList (code1 baselineCompilerConfig.dataConf BackendStages.Native.stack))
    (s2 baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf entryHeapLimit entrySp
      riscvConfig.addrOffset BackendStages.Native.stack
      (LabToTarget.baselineLabState input cfg asm memory bitmapDomain sharedDomain)
      entrySaveRegs (entryStackOracle cfg)) = some source
  wordInitialized : WordToStack.InitializationPremises riscvConfig BackendStages.Native.programs0
    (entryStackState cfg source) (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (entryWordOracle cfg)
  nativeBound : ∀ fuel post outcome,
    LabSem.evaluate {LabToTarget.baselineLabState input cfg asm memory bitmapDomain sharedDomain
      with clock := fuel} = (.halt outcome, post) →
    ∃ count native, count ≤ 14467153 * fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome, native, post.ffi)

/-- All entry witnesses exist from checked source, compilation and installation
certificates, with no static or execution assumptions supplied by the caller. -/
theorem baselineRuntimeEntry_exists (input : Guest.InputBlob) : Nonempty (BaselineRuntimeEntry input) := by
  obtain ⟨cfg, asm, memory, bitmapDomain, sharedDomain, i, agreement, shared, guards, assumptions⟩ :=
    LabToTarget.baseline_actual_joint_initialization input
  obtain ⟨source, selected, wordInit⟩ := WordToStack.selected_word_initialization riscvConfig
    baselineCompilerConfig.wordToWordConf sourceDeclarations [] BackendStages.Native.programs0
    InitECandidate.bitmaps BackendStages.Native.wordConfig (0 :: BackendStages.Native.frames0)
    BackendStages.Native.stack cfg baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
    entryHeapLimit entrySp riscvConfig.addrOffset
    (LabToTarget.baselineLabState input cfg asm memory bitmapDomain sharedDomain) entrySaveRegs 0
    (Or.inr rfl) (by decide) (by decide) LabToTarget.baseline_word_program
    BackendStages.Native.native_submitted_bitmaps_eq assumptions
  refine ⟨⟨cfg, asm, memory, bitmapDomain, sharedDomain, source, agreement, shared,
    assumptions, selected, wordInit, ?_⟩⟩
  intro fuel post outcome run
  obtain ⟨count, native, bound, nativeRun⟩ := LabToTarget.actual_aligned_compiled_native_bound
    baselineMachineConfig (sourceFfi input) baselineInstalledState riscvConfig
    baselineCompilerConfig.labConf cfg InitECandidate.nativeCode 620 i asm memory _ sharedDomain _
    guards fuel post outcome rfl run
  exact ⟨count, native, by simpa only [LiteralFacts.nativeCode_length] using bound, nativeRun⟩

#print axioms baselineRuntimeEntry_exists
end InitECandidate.Runtime
