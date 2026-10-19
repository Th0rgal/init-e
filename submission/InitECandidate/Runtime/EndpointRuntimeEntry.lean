import InitECandidate.Runtime.EndpointWordMemoryActualJoint
import InitECandidate.Runtime.BaselineWordMemoryEntry
import InitECandidate.Runtime.BaselineInstalledRegisters
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
structure EndpointRuntimeEntry (input : Guest.InputBlob) (endpoint : riscv_state) where
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
    (LabToTarget.endpointLabState input endpoint cfg asm memory bitmapDomain sharedDomain)
    entrySaveRegs 0 (entryStackOracle cfg)
  selection : StackRemove.Proofs.InitMake.makeInitOpt
    (StackToLab.isGenGc baselineCompilerConfig.dataConf.gcKind) entryHeapLimit InitECandidate.bitmaps
    0 (coracle1 (entryStackOracle cfg)) baselineCompilerConfig.stackConf.jump riscvConfig.addrOffset
    entrySp (sptFromAList (code1 baselineCompilerConfig.dataConf BackendStages.Native.stack))
    (s2 baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf entryHeapLimit entrySp
      riscvConfig.addrOffset BackendStages.Native.stack
      (LabToTarget.endpointLabState input endpoint cfg asm memory bitmapDomain sharedDomain)
      entrySaveRegs (entryStackOracle cfg)) = some source
  wordInitialized : WordToStack.InitializationPremises riscvConfig BackendStages.Native.programs0
    (entryStackState cfg source) (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (entryWordOracle cfg)
  nativeBound : ∀ fuel post outcome,
    LabSem.evaluate {LabToTarget.endpointLabState input endpoint cfg asm memory bitmapDomain sharedDomain
      with clock := fuel} = (.halt outcome, post) →
    ∃ count native, count ≤ 14467153 * fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome, native, post.ffi)

theorem endpointRuntimeEntry_exists (input : Guest.InputBlob) (endpoint : riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) :
    ∃ entry : EndpointRuntimeEntry input endpoint, (∀ address, entry.source.mdomain address = true → ∃ word, entry.source.memory address = WordLocW.word word) ∧
      entry.asm.regs 11 = BitVec.ofNat 64 sourceBase ∧
      entry.asm.regs 12 = BitVec.ofNat 64 stackStart ∧
      entry.asm.regs 13 = BitVec.ofNat 64 ramEnd := by
  obtain ⟨cfg,asm,memory,bitmapDomain,sharedDomain,i,words,agreement,shared,guards,assumptions⟩ :=
    LabToTarget.WordMemory.endpoint_word_actual_joint_initialization input endpoint related
  obtain ⟨source,selected,wordInit⟩ := WordToStack.selected_word_initialization riscvConfig
    baselineCompilerConfig.wordToWordConf sourceDeclarations [] BackendStages.Native.programs0
    InitECandidate.bitmaps BackendStages.Native.wordConfig (0 :: BackendStages.Native.frames0)
    BackendStages.Native.stack cfg baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
    entryHeapLimit entrySp riscvConfig.addrOffset
    (LabToTarget.endpointLabState input endpoint cfg asm memory bitmapDomain sharedDomain) entrySaveRegs 0
    (Or.inr rfl) (by decide) (by decide) LabToTarget.baseline_word_program
    BackendStages.Native.native_submitted_bitmaps_eq assumptions
  have nativeBound : ∀ fuel post outcome,
      LabSem.evaluate {LabToTarget.endpointLabState input endpoint cfg asm memory bitmapDomain sharedDomain with clock := fuel} =
        (.halt outcome,post) → ∃ count native, count ≤ 14467153 * fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint = (.halt outcome,native,post.ffi) := by
    intro fuel post outcome run
    obtain ⟨count,native,bound,nativeRun⟩ := LabToTarget.actual_aligned_compiled_native_bound
      baselineMachineConfig (sourceFfi input) endpoint riscvConfig
      baselineCompilerConfig.labConf cfg InitECandidate.nativeCode 620 i asm memory _ sharedDomain _
      guards fuel post outcome rfl run
    exact ⟨count,native,by simpa only [LiteralFacts.nativeCode_length] using bound,nativeRun⟩
  let entry : EndpointRuntimeEntry input endpoint :=
    ⟨cfg,asm,memory,bitmapDomain,sharedDomain,source,agreement,shared,assumptions,selected,wordInit,nativeBound⟩
  refine ⟨entry,?_,?_⟩
  · exact StackRemove.selected_words_of_full_initialization baselineCompilerConfig.stackConf
      baselineCompilerConfig.dataConf entryHeapLimit entrySp riscvConfig.addrOffset InitECandidate.bitmaps
      BackendStages.Native.stack (LabToTarget.endpointLabState input endpoint cfg asm memory bitmapDomain sharedDomain)
      entrySaveRegs 0 (entryStackOracle cfg) assumptions words source selected

  · have agreement := baseline_endpoint_agreement endpoint related
    have canonical := machineStateOfAsm_relation installedAsm (by decide)
    have reverse : InstallationAgreement baselineMachineConfig endpoint baselineInstalledState :=
      ⟨canonical.1, agreement.pc.symm,
       fun a ha => (agreement.bytes a ha).symm,
       fun r hr => (agreement.regs r hr).symm,
       fun r hr => (agreement.fpRegs r hr).symm⟩
    exact baseline_good_init_registers asm memory _ sharedDomain
      (goodInitState_transport reverse guards.2.2.2.2.2.2.2.2.1)


end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.endpointRuntimeEntry_exists
