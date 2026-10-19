-- Endpoint-parameterized copies of existing participant proofs.
-- Original static compiler/source facts are reused unchanged.
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.BaselineCompiledFunctions
import InitECandidate.Runtime.BaselineCrepLoopEntryAffine
import InitECandidate.Runtime.BaselineCrepNativeAffine
import InitECandidate.Runtime.BaselineFrontendLayout
import InitECandidate.Runtime.BaselineFrontendNativeAffine
import InitECandidate.Runtime.BaselineGlobalEntry
import InitECandidate.Runtime.BaselineGlobalFunctionTable
import InitECandidate.Runtime.BaselineGlobalsClock
import InitECandidate.Runtime.BaselineGlobalsLayout
import InitECandidate.Runtime.BaselineHeapLayoutFacts
import InitECandidate.Runtime.BaselineInstalledRegisters
import InitECandidate.Runtime.BaselineLoopNativeAffine
import InitECandidate.Runtime.BaselineNativeOutcomesAffine
import InitECandidate.Runtime.BaselinePanDeclarationSetup
import InitECandidate.Runtime.BaselineSourceFunctionsSetup
import InitECandidate.Runtime.BaselineWordMemoryEntry
import InitECandidate.Runtime.CanonicalCrepNativeAffine
import InitECandidate.Runtime.CanonicalGlobalNative
import InitECandidate.Runtime.CanonicalGlobalNativeAffine
import InitECandidate.Runtime.CanonicalGlobalsFunctionRelation
import InitECandidate.Runtime.CanonicalGlobalsInitialRelation
import InitECandidate.Runtime.CanonicalGlobalsInitialization
import InitECandidate.Runtime.CanonicalGlobalsReady
import InitECandidate.Runtime.CanonicalHeapLayout
import InitECandidate.Runtime.CanonicalInitializedNative
import InitECandidate.Runtime.CanonicalInitializedNativeAffine
import InitECandidate.Runtime.CanonicalOriginalNative
import InitECandidate.Runtime.CanonicalOriginalSourceEntry
import InitECandidate.Runtime.CanonicalPanDeclarations
import InitECandidate.Runtime.CanonicalPanNative
import InitECandidate.Runtime.CanonicalPanNativeAffine
import InitECandidate.Runtime.CanonicalRenamedNative
import InitECandidate.Runtime.CanonicalRenamedNativeAffine
import InitECandidate.Runtime.CanonicalSourceDeclarations
import InitECandidate.Runtime.CanonicalSourceEntryFields
import InitECandidate.Runtime.CanonicalSourceExceptionsEvaluated
import InitECandidate.Runtime.CanonicalSourceFunctionsEvaluated
import InitECandidate.Runtime.CanonicalSourceLayout
import InitECandidate.Runtime.CanonicalSourceState
import InitECandidate.Runtime.CanonicalUnrenamedNative
import InitECandidate.Runtime.CanonicalUnrenamedNativeAffine
import InitECandidate.Runtime.CompilationInstallationTransport
import InitECandidate.Runtime.CrepAffine
import InitECandidate.Runtime.CrepEntryAffine
import InitECandidate.Runtime.CrepWholeEntryAffine
import InitECandidate.Runtime.EndpointCanonicalPanNativeAffine
import InitECandidate.Runtime.PanDeclarationSetup
import InitECandidate.Runtime.PanFunctionRenameClock
import InitECandidate.Runtime.PanGlobalsCodeRelation
import InitECandidate.Runtime.PanInitCallClock
import InitECandidate.Runtime.PanRenameRun
import InitECandidate.Runtime.PanSimpDeclarationReflection
import InitECandidate.Runtime.PanSimpEntryClock
import InitECandidate.Runtime.SelectedFullInitialization
import InitECandidate.Runtime.SelectedFullInitializerFields
import InitECandidate.Runtime.SelectedInitializerClock
import InitECandidate.Runtime.SourceClock
import InitECandidate.Runtime.SourceEntryCode
import InitECandidate.Runtime.ZeroGlobalDeclarations
import InitECandidate.Runtime.ZeroGlobalsFrame

-- Original module: BaselineSourceRegisterEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics


def endpoint_EntrySourceRegisters {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) : Prop :=
  entry.asm.regs 11 = BitVec.ofNat 64 sourceBase ∧
  entry.asm.regs 12 = BitVec.ofNat 64 stackStart ∧
  entry.asm.regs 13 = BitVec.ofNat 64 ramEnd

end InitECandidate.Runtime

-- Original module: CanonicalPanDeclarations
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Global-lowered declaration state before the original evaluator installs
functions and exception shapes. Runtime fields are the canonical initialized ones. -/

noncomputable def endpoint_canonicalPanDeclarationState (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  {endpoint_canonicalPanEntryState input endpoint endpointRelated with code := HolFiniteMapExact.empty, eshapes := HolFiniteMapExact.empty}

end InitECandidate.Runtime

-- Original module: BaselineInitializerFields
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend

/-- Exact fields of the selected initialized state, derived solely from its
original full initialization assumptions and successful optional selection. -/

theorem endpoint_entry_selected_fields {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :
    entry.source.ffi = sourceFfi input ∧
      entry.source.store.lookup .currHeap = some (.word
        (entry.asm.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2))) := by
  exact StackRemove.selected_fields_of_full_initialization baselineCompilerConfig.stackConf
    baselineCompilerConfig.dataConf entryHeapLimit entrySp
    Compiler.Encoders.RiscV.Target.riscvConfig.addrOffset InitECandidate.bitmaps BackendStages.Native.stack
    (LabToTarget.endpointLabState input endpoint entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain)
    entrySaveRegs 0 (entryStackOracle entry.cfg) entry.stackAssumptions entry.source entry.selection

theorem endpoint_entry_frontend_ffi {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :
    (endpointFrontendState entry).ffi = sourceFfi input := by
  change entry.source.ffi = sourceFfi input
  exact (endpoint_entry_selected_fields entry).1

theorem endpoint_canonical_pan_entry_ffi (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanEntryState input endpoint endpointRelated).ffi = sourceFfi input :=
  endpoint_entry_frontend_ffi (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)

theorem endpoint_canonical_pan_declaration_ffi (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).ffi = sourceFfi input :=
  endpoint_canonical_pan_entry_ffi input endpoint endpointRelated

theorem endpoint_entry_frontend_heap_register {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :
    (endpointFrontendState entry).store.lookup .currHeap = some (.word
      (entry.asm.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2))) := by
  change (entry.source.store.eraseEq .handler).lookup .currHeap = _
  simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using (endpoint_entry_selected_fields entry).2

theorem endpoint_canonical_heap_base_register (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    endpoint_canonicalHeapBase input endpoint endpointRelated = (endpoint_canonicalRuntimeEntry input endpoint endpointRelated).asm.regs
      (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2) := by
  obtain ⟨capacity,_,_,_,_,_,_,heap,_⟩ := endpoint_canonical_loop_related input endpoint endpointRelated
  have installed := endpoint_entry_frontend_heap_register (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)
  have equal := Option.some.inj (heap.symm.trans installed)
  exact WordLocW.word.inj equal

theorem endpoint_canonical_heap_base_source (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    endpoint_canonicalHeapBase input endpoint endpointRelated = BitVec.ofNat 64 sourceBase := by
  rw [endpoint_canonical_heap_base_register]
  have name : StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2 = 11 := by decide_cbv
  rw [name]
  exact (endpoint_canonical_source_registers input endpoint endpointRelated).1

theorem endpoint_canonical_pan_declaration_base (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).baseAddr = BitVec.ofNat 64 sourceBase :=
  endpoint_canonical_heap_base_source input endpoint endpointRelated

end InitECandidate.Runtime

-- Original module: BaselineFrontendLayout
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend Classical
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Pancake.Proofs.PanToTarget

/-- The actual selected initializer is the full initializer's exact result. -/

theorem endpoint_entry_fullMakeInit {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :
    fullMakeInit baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf entryHeapLimit entrySp
      riscvConfig.addrOffset InitECandidate.bitmaps BackendStages.Native.stack
      (LabToTarget.endpointLabState input endpoint entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain)
      entrySaveRegs 0 (entryStackOracle entry.cfg) =
      (entryStackState entry.cfg entry.source,some entry.source) := by
  rw [fullMakeInit_eq]
  simp only [entry.selection,StackRemove.Proofs.InitMake.makeInitAny]
  rfl

theorem endpoint_entry_lab_pointers {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (regs : endpoint_EntrySourceRegisters entry) :
    let lab := LabToTarget.endpointLabState input endpoint entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain
    lab.regs lab.lenReg = .word (BitVec.ofNat 64 sourceBase) ∧
    lab.regs lab.ptr2Reg = .word (BitVec.ofNat 64 stackStart) ∧
    lab.regs lab.len2Reg = .word (BitVec.ofNat 64 ramEnd) := by
  exact ⟨congrArg WordLocW.word regs.1,congrArg WordLocW.word regs.2.1,congrArg WordLocW.word regs.2.2⟩

theorem endpoint_entry_frontend_domain {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (regs : endpoint_EntrySourceRegisters entry) (address : BitVec 64) :
    (endpointFrontendState entry).mdomain address =
      decide (StackRemove.addresses (BitVec.ofNat 64 sourceBase)
        (((BitVec.ofNat 64 stackStart) + -1 * BitVec.ofNat 64 sourceBase).toNat / 8) address) := by
  have ptr := endpoint_entry_lab_pointers entry regs
  exact panToTargetWordInitMdomain (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList BackendStages.Native.programs0) (worac := entryWordOracle entry.cfg)
    (BitVec.ofNat 64 sourceBase) (BitVec.ofNat 64 stackStart) (BitVec.ofNat 64 ramEnd)
    entry.stackAssumptions (endpoint_entry_fullMakeInit entry) ptr.1 ptr.2.1 ptr.2.2
    baseline_heap_low baseline_heap_high baseline_heap_fits baseline_heap_limit_fits baseline_heap_aligned address

theorem endpoint_entry_frontend_heap_length {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (regs : endpoint_EntrySourceRegisters entry) :
    (endpointFrontendState entry).store.lookup .heapLength = some (.word
      (BitVec.ofNat 64 (StackRemove.Proofs.InitLimits.getStackHeapLimit entryHeapLimit
        (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 stackStart,BitVec.ofNat 64 ramEnd)).2 * StackRemove.bytesInWord 64)) := by
  have ptr := endpoint_entry_lab_pointers entry regs
  obtain ⟨base,found,current,length⟩ := panToTargetWordInitStore (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList BackendStages.Native.programs0) (worac := entryWordOracle entry.cfg)
    entry.stackAssumptions (endpoint_entry_fullMakeInit entry)
  rw [readPointers_s2 entry.stackAssumptions ptr.1 ptr.2.1 ptr.2.2] at length
  exact length

theorem endpoint_entry_frontend_heap_memory {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (address : BitVec 64) (valid : (endpointFrontendState entry).mdomain address = true) :
    (endpointFrontendState entry).memory address = entry.memory address := by
  have fields := panToTargetWordInitMemory (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList BackendStages.Native.programs0) (worac := entryWordOracle entry.cfg)
    entry.stackAssumptions (endpoint_entry_fullMakeInit entry)
  exact fields.2.2.2 address valid

end InitECandidate.Runtime

-- Original module: CanonicalHeapLayout
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend Classical
open Flapjack.Pancake.Proofs.PanToTarget


theorem endpoint_canonical_heap_length_store (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpointFrontendState (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)).store.lookup .heapLength = some (.word baselineHeapLength) :=
  endpoint_entry_frontend_heap_length _ (endpoint_canonical_source_registers input endpoint endpointRelated)

theorem endpoint_canonical_pan_heap_top (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).topAddr = BitVec.ofNat 64 stackStart := by
  obtain ⟨capacity,_,_,_,_,_,_,_,length,top,_⟩ := endpoint_canonical_loop_related input endpoint endpointRelated
  have stored := endpoint_canonical_heap_length_store input endpoint endpointRelated
  have equal := WordLocW.word.inj (Option.some.inj (length.symm.trans stored))
  rw [equal] at top
  change (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).topAddr = endpoint_canonicalHeapBase input endpoint endpointRelated + 2 * baselineHeapLength at top
  rw [endpoint_canonical_heap_base_source,baseline_heap_top] at top
  exact top

theorem endpoint_canonical_pan_memory_domain (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).memaddrs =
      StackRemove.addresses (BitVec.ofNat 64 sourceBase) ((stackStart-sourceBase)/8) := by
  funext address
  change ((endpointFrontendState (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)).mdomain address = true) = _
  rw [endpoint_entry_frontend_domain _ (endpoint_canonical_source_registers input endpoint endpointRelated),baseline_heap_word_count]
  simp only [decide_eq_true_eq]

theorem endpoint_canonical_pan_memory_domain_split (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).memaddrs = fun address =>
      ordinaryDomain address ∨ StackRemove.addresses (BitVec.ofNat 64 heapEnd) globalsWords address := by
  rw [endpoint_canonical_pan_memory_domain]
  have split := addressesSplitGlobals (width := 64) (Or.inr rfl) (BitVec.ofNat 64 sourceBase)
    ((stackStart-sourceBase)/8) globalsWords (by decide)
  rw [baseline_globals_tail] at split
  exact split.symm

theorem endpoint_canonical_pan_memory_agreement (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) (address : BitVec 64)
    (valid : (sourceInitialState input).memaddrs address) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).memory address = (sourceInitialState input).memory address := by
  have whole : (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).memaddrs address := by
    rw [endpoint_canonical_pan_memory_domain_split]
    exact Or.inl valid
  have actual := endpoint_entry_frontend_heap_memory (endpoint_canonicalRuntimeEntry input endpoint endpointRelated) address whole
  have source := (endpoint_canonicalRuntimeEntry input endpoint endpointRelated).memoryAgreement address valid
  change wlocWlabHOL ((endpointFrontendState (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)).memory address) = _
  rw [actual,source]
  rfl

end InitECandidate.Runtime

-- Original module: CanonicalSourceLayout
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget


theorem endpoint_entry_frontend_endian_shared {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :
    (endpointFrontendState entry).be = false ∧
    (endpointFrontendState entry).shMdomain =
      (LabToTarget.endpointLabState input endpoint entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain).sharedMemDomain := by
  have fields := panToTargetWordInitMemory (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList BackendStages.Native.programs0) (worac := entryWordOracle entry.cfg)
    entry.stackAssumptions (endpoint_entry_fullMakeInit entry)
  exact ⟨fields.2.1,fields.2.2.1⟩

theorem endpoint_canonical_pan_endian (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).be = (sourceInitialState input).be :=
  (endpoint_entry_frontend_endian_shared (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)).1

theorem endpoint_canonical_pan_shared_domain (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).shMemaddrs = (sourceInitialState input).shMemaddrs := by
  funext address
  change ((endpointFrontendState (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)).shMdomain address = true) = _
  rw [congrFun (endpoint_entry_frontend_endian_shared (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)).2 address]
  change (((endpoint_canonicalRuntimeEntry input endpoint endpointRelated).sharedDomain address && holByteAligned address) = true) = _
  simpa only [Bool.and_eq_true] using (congrFun (endpoint_canonicalRuntimeEntry input endpoint endpointRelated).sharedAgreement address).symm

theorem endpoint_canonical_pan_source_top (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).topAddr =
      (sourceInitialState input).topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsWords := by
  rw [endpoint_canonical_pan_heap_top,source_top_with_globals]

theorem endpoint_canonical_pan_source_domain (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).memaddrs = fun address =>
      (sourceInitialState input).memaddrs address ∨
        StackRemove.addresses (sourceInitialState input).topAddr globalsWords address :=
  endpoint_canonical_pan_memory_domain_split input endpoint endpointRelated

end InitECandidate.Runtime

-- Original module: CanonicalSourceClock
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit


theorem endpoint_entry_frontend_clock_zero {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :
    (endpointFrontendState entry).clock = 0 := by
  have bound := StackRemove.selected_clock_le (StackToLab.isGenGc baselineCompilerConfig.dataConf.gcKind)
    entryHeapLimit InitECandidate.bitmaps 0 (coracle1 (entryStackOracle entry.cfg))
    baselineCompilerConfig.stackConf.jump riscvConfig.addrOffset entrySp
    (sptFromAList (code1 baselineCompilerConfig.dataConf BackendStages.Native.stack))
    (s2 baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf entryHeapLimit entrySp
      riscvConfig.addrOffset BackendStages.Native.stack
      (LabToTarget.endpointLabState input endpoint entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain)
      entrySaveRegs (entryStackOracle entry.cfg)) entry.source entry.selection
  change entry.source.clock ≤ 0 at bound
  change entry.source.clock = 0
  exact Nat.le_zero.mp bound

theorem endpoint_canonical_pan_declaration_clock (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).clock = (sourceInitialState input).clock :=
  endpoint_entry_frontend_clock_zero (endpoint_canonicalRuntimeEntry input endpoint endpointRelated)

end InitECandidate.Runtime

-- Original module: BaselineGlobalsLayout
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Compiler.Backend

/-- Reserving the globals tail does not overlap any ordinary source word. -/

theorem endpoint_canonical_pan_top_outside (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    ¬ (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).memaddrs
      (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).topAddr := by
  rw [endpoint_canonical_pan_memory_domain,endpoint_canonical_pan_heap_top]
  have top : (BitVec.ofNat 64 sourceBase) + panBytesInWord 64 *
      BitVec.ofNat 64 ((stackStart-sourceBase)/8) = BitVec.ofNat 64 stackStart := by decide_cbv
  rw [← top]
  exact PanGlobalsCompileTopSemanticsDecls.topNotInAddresses (Or.inr rfl) _ _ (by decide)

end InitECandidate.Runtime

-- Original module: CanonicalGlobalsInitialRelation
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

/-- Original source runtime before global declarations, after exception setup. -/

noncomputable def endpoint_canonicalGlobalsSourceState (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {sourceInitialState input with eshapes := (endpoint_canonicalPanEntryState input endpoint endpointRelated).eshapes}

theorem endpoint_canonical_globals_initial_relation (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    panGlobalsStateRelHOLExact false FrontendStages.Declarations.globalInitial
      (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) (endpoint_canonicalPanEntryState input endpoint endpointRelated) := by
  classical
  unfold panGlobalsStateRelHOLExact
  refine ⟨?_,?_,?_,?_,rfl,?_,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,Or.inr rfl⟩
  · change (sourceInitialState input).topAddr =
      (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).topAddr -
        FrontendStages.Declarations.globalInitial.maxGlobalsSize
    rw [endpoint_canonical_pan_source_top]
    change _ = _ + panBytesInWord 64 * BitVec.ofNat 64 globalsWords -
      cakeBytesInWord 64 * BitVec.ofNat 64 93
    have bytes : cakeBytesInWord 64 = panBytesInWord 64 := by decide_cbv
    rw [bytes]
    change _ = _ + panBytesInWord 64 * 93#64 - panBytesInWord 64 * 93#64
    rw [BitVec.add_sub_cancel]
  · intro impossible; cases impossible
  · exact (endpoint_canonical_pan_declaration_base input endpoint endpointRelated).symm
  · exact (endpoint_canonical_pan_endian input endpoint endpointRelated).symm
  · exact (endpoint_canonical_pan_declaration_clock input endpoint endpointRelated).symm
  · intro name value lookup; cases lookup
  · intro name shape address lookup; cases lookup
  · intro address valid
    change (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).memaddrs address
    rw [endpoint_canonical_pan_source_domain]
    exact Or.inl valid
  · exact (endpoint_canonical_pan_shared_domain input endpoint endpointRelated).symm
  · intro address valid
    exact (endpoint_canonical_pan_memory_agreement input endpoint endpointRelated address valid).symm
  · exact (endpoint_canonical_pan_declaration_ffi input endpoint endpointRelated).symm
  · intro name params body shape lookup; cases lookup
  · intro name1 name2 shape1 address1 shape2 address2 different present
    exact (present rfl).elim
  · exact endpoint_canonical_pan_top_outside input endpoint endpointRelated
  · change panGlobalsByteAlignedHOL (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).topAddr
    rw [endpoint_canonical_pan_heap_top]
    exact baseline_globals_top_aligned

end InitECandidate.Runtime

-- Original module: CanonicalGlobalsInitialization
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact


theorem endpoint_canonical_globals_initialize (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (sourcePost : PanSemStateFiniteExact 64 Guest.HostMemory)
    (sourceRun : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated)
      (fun address => Classical.propDecidable ((endpoint_canonicalGlobalsSourceState input endpoint endpointRelated).memaddrs address))
      FrontendStages.Declarations.globalDeclarations = some sourcePost) :
    ∃ initialized, evaluateHOLFiniteState (endpoint_canonicalPanEntryState input endpoint endpointRelated)
        (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized) ∧
      panGlobalsStateRelHOLExact false FrontendStages.Declarations.globalContext sourcePost initialized ∧
      initialized.clock = (endpoint_canonicalPanEntryState input endpoint endpointRelated).clock ∧
      initialized.ffi = (endpoint_canonicalPanEntryState input endpoint endpointRelated).ffi ∧
      initialized.locals = (endpoint_canonicalPanEntryState input endpoint endpointRelated).locals ∧
      panGlobalsByteAlignedHOL FrontendStages.Declarations.globalContext.globalsSize := by
  classical
  apply PanGlobalsInitGlobalsAssembly.initGlobalsAll (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated)
    FrontendStages.Declarations.globalDeclarations FrontendStages.Declarations.globalInitial
    sourcePost FrontendStages.Declarations.globalInitializers [] []
    FrontendStages.Declarations.globalContext (endpoint_canonicalPanEntryState input endpoint endpointRelated)
    (Compiler.Backend.StackRemove.addresses (BitVec.ofNat 64 heapEnd) globalsWords)
  refine ⟨sourceRun,List.all_eq_true.mp baseline_global_declarations_kind,
    FrontendStages.Declarations.compileGlobals_eq,endpoint_canonical_globals_initial_relation input endpoint endpointRelated,
    ?_,?_,?_,?_,rfl,?_,?_⟩
  · rw [baseline_global_declarations_words]
    change _ = Compiler.Backend.StackRemove.addresses
      ((endpoint_canonicalPanDeclarationState input endpoint endpointRelated).topAddr - panBytesInWord 64 * BitVec.ofNat 64 globalsWords - 0)
      globalsWords
    rw [endpoint_canonical_pan_source_top]
    simp only [BitVec.add_sub_cancel,sub_zero]
    rfl
  · exact baseline_globals_disjoint
  · intro address valid
    change (endpoint_canonicalPanDeclarationState input endpoint endpointRelated).memaddrs address
    rw [endpoint_canonical_pan_memory_domain_split]
    exact Or.inr valid
  · exact PanGlobalsCompileTopSemanticsDecls.alignedZero
  · intro name shape address present
    exact (Bool.noConfusion present.1)
  · rw [baseline_global_declarations_words]
    exact baseline_globals_size_fits

end InitECandidate.Runtime

-- Original module: ZeroGlobalDeclarations
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact


theorem endpoint_canonical_source_globals_evaluate (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated)
      (fun address => Classical.propDecidable ((endpoint_canonicalGlobalsSourceState input endpoint endpointRelated).memaddrs address))
      FrontendStages.Declarations.globalDeclarations =
      some (zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames) := by
  classical
  rw [baseline_global_declarations_zero]
  exact zero_global_declarations_evaluate _ _

end InitECandidate.Runtime

-- Original module: CanonicalGlobalsReady
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The fixed source globals always initialize on the actual installed memory. -/

theorem endpoint_canonical_globals_ready (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    ∃ initialized, evaluateHOLFiniteState (endpoint_canonicalPanEntryState input endpoint endpointRelated)
        (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized) ∧
      panGlobalsStateRelHOLExact false FrontendStages.Declarations.globalContext (zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames) initialized ∧
      initialized.clock = (endpoint_canonicalPanEntryState input endpoint endpointRelated).clock ∧
      initialized.ffi = (endpoint_canonicalPanEntryState input endpoint endpointRelated).ffi ∧
      initialized.locals = (endpoint_canonicalPanEntryState input endpoint endpointRelated).locals ∧
      panGlobalsByteAlignedHOL FrontendStages.Declarations.globalContext.globalsSize :=
  endpoint_canonical_globals_initialize input endpoint endpointRelated _ (endpoint_canonical_source_globals_evaluate input endpoint endpointRelated)

noncomputable def endpoint_canonicalInitializedGlobals (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  Classical.choose (endpoint_canonical_globals_ready input endpoint endpointRelated)

theorem endpoint_canonical_globals_ready_run (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    evaluateHOLFiniteState (endpoint_canonicalPanEntryState input endpoint endpointRelated)
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) =
      (none,endpoint_canonicalInitializedGlobals input endpoint endpointRelated) :=
  (Classical.choose_spec (endpoint_canonical_globals_ready input endpoint endpointRelated)).1

theorem endpoint_canonical_globals_ready_relation (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    panGlobalsStateRelHOLExact false FrontendStages.Declarations.globalContext
      (zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames)
      (endpoint_canonicalInitializedGlobals input endpoint endpointRelated) :=
  (Classical.choose_spec (endpoint_canonical_globals_ready input endpoint endpointRelated)).2.1

end InitECandidate.Runtime

-- Original module: BaselineGlobalEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact


theorem endpoint_baseline_pan_generated_main (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanEntryState input endpoint endpointRelated).code.lookup baselineCrepStart = some ([],
      .seq (nestedSeqHOL FrontendStages.Declarations.globalInitializers)
        (.call none FrontendStages.Declarations.globalNewStart []),.one) := by
  calc
    _ = List.lookup baselineCrepStart (functionsHOL FrontendStages.pass2) :=
      FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _
    _ = _ := by kernel_rfl

theorem endpoint_baseline_pan_renamed_main (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalPanEntryState input endpoint endpointRelated).code.lookup FrontendStages.Declarations.globalNewStart =
      some ([],baselineRenamedMainBody,.one) := by
  calc
    _ = List.lookup FrontendStages.Declarations.globalNewStart (functionsHOL FrontendStages.pass2) :=
      FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _
    _ = _ := by
      have name : (match FrontendStages.Declarations.globalOutput0 with
        | .function decl => decl.name | _ => baselineCrepStart) =
          FrontendStages.Declarations.globalNewStart := by decide_cbv
      simp only [FrontendStages.pass2, FrontendStages.Declarations.exceptionDeclarations,
        FrontendStages.generatedMain, FrontendStages.Declarations.translatedFunctions,
        functionsHOL, List.lookup, baselineRenamedMainBody]
      simp_all only [FrontendStages.Declarations.globalOutput0, declToHOL, funDeclToHOL,
        FrontendStages.Declarations.globalData0, List.map_nil, shapeToHOL]
      kernel_rfl

theorem endpoint_canonical_global_entry_one_clock (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (initialized : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initialRun : evaluateHOLFiniteState {endpoint_canonicalPanEntryState input endpoint endpointRelated with locals := HolFiniteMapExact.empty}
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized))
    (clock : initialized.clock = (endpoint_canonicalPanEntryState input endpoint endpointRelated).clock)
    (fuel : Nat) (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState {initialized with clock := fuel}
      (.call none FrontendStages.Declarations.globalNewStart []) = (result,post)) :
    ∃ final, evaluateHOLFiniteState {endpoint_canonicalPanEntryState input endpoint endpointRelated with clock := fuel + 1}
      (.call none baselineCrepStart []) = (result,final) ∧ final.ffi = post.ffi :=
  pan_init_call_one_clock (endpoint_canonicalPanEntryState input endpoint endpointRelated) initialized baselineCrepStart
    FrontendStages.Declarations.globalNewStart (nestedSeqHOL FrontendStages.Declarations.globalInitializers)
    baselineRenamedMainBody [] .one (endpoint_baseline_pan_generated_main input endpoint endpointRelated) (endpoint_baseline_pan_renamed_main input endpoint endpointRelated)
    initialRun clock fuel result post run

end InitECandidate.Runtime

-- Original module: BaselineGlobalFunctionTable
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang


private theorem endpoint_lookup_member_distinct {A B : Type} [BEq A] [LawfulBEq A]
    (entries : List (A × B)) (name : A) (value : B)
    (member : (name,value) ∈ entries) (distinct : (entries.map Prod.fst).Nodup) :
    List.lookup name entries = some value := by
  induction entries with
  | nil => simp at member
  | cons entry entries ih =>
    obtain ⟨key,entryValue⟩ := entry
    simp only [List.map_cons,List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with equal | member
    · cases equal; simp
    · have different : name ≠ key := by
        intro equal
        have present : name ∈ entries.map Prod.fst := List.mem_map.mpr ⟨(name,value),member,rfl⟩
        exact distinct.1 (equal ▸ present)
      simp only [List.lookup_cons,show (name == key) = false by simp [different]]
      exact ih member distinct.2

theorem endpoint_canonical_compiled_function_lookup (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (name : MlS) (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (member : (name,params,body,shape) ∈
      functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations) :
    (endpoint_canonicalPanEntryState input endpoint endpointRelated).code.lookup name =
      some (params,compileProgExactHOL FrontendStages.Declarations.globalContext body,shape) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL FrontendStages.pass2).reverse).lookup name = _
  calc
    _ = List.lookup name (functionsHOL FrontendStages.pass2) := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _
    _ = _ := by
      apply endpoint_lookup_member_distinct _ _ _ _ baseline_pan_distinct
      rw [baseline_global_function_table]
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨(name,params,body,shape),member,rfl⟩

end InitECandidate.Runtime

-- Original module: CanonicalGlobalsFunctionRelation
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Initialization preserves the actual installed function table. -/

theorem endpoint_canonical_globals_ready_code (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalInitializedGlobals input endpoint endpointRelated).code = (endpoint_canonicalPanEntryState input endpoint endpointRelated).code := by
  have invariant := evaluateInvariantsHOLFinite
    (nestedSeqHOL FrontendStages.Declarations.globalInitializers)
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (endpoint_canonicalPanEntryState input endpoint endpointRelated)) none
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (endpoint_canonicalInitializedGlobals input endpoint endpointRelated)) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite,endpoint_canonical_globals_ready_run])
  exact invariant.2.2.2.2.2.2.1

noncomputable def endpoint_canonicalRenamedSourceEntry (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  sourceEntryCode (zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames)
    (endpoint_canonicalInitializedGlobals input endpoint endpointRelated).locals
    (HolFiniteMapExact.empty.updateList
      (functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations).reverse)

private theorem endpoint_lookup_member {A B : Type} [BEq A] [LawfulBEq A]
    (entries : List (A × B)) (name : A) (value : B)
    (lookup : List.lookup name entries = some value) : (name,value) ∈ entries := by
  induction entries with
  | nil => simp at lookup
  | cons entry entries ih =>
    obtain ⟨key,entryValue⟩ := entry
    by_cases equal : name = key
    · subst equal; simp at lookup; subst lookup; simp
    · simp only [List.lookup_cons,show (name == key) = false by simp [equal]] at lookup
      exact List.mem_cons_of_mem _ (ih lookup)

theorem endpoint_canonical_globals_function_relation (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) (fuel : Nat) :
    panGlobalsStateRelHOLExact true FrontendStages.Declarations.globalContext
      {endpoint_canonicalRenamedSourceEntry input endpoint endpointRelated with clock := fuel}
      {endpoint_canonicalInitializedGlobals input endpoint endpointRelated with clock := fuel} := by
  apply pan_globals_relation_clock
  apply pan_globals_install_code _ _ _ _ (endpoint_canonical_globals_ready_relation input endpoint endpointRelated)
  intro name params body shape lookup
  have sourceLookup : List.lookup name
      (functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations) = some (params,body,shape) := by
    exact (FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _).symm.trans lookup
  rw [endpoint_canonical_globals_ready_code]
  exact endpoint_canonical_compiled_function_lookup input endpoint endpointRelated name params body shape (endpoint_lookup_member _ _ _ sourceLookup)

end InitECandidate.Runtime

-- Original module: PanFunctionRenameClock
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact


noncomputable def endpoint_canonicalUnrenamedSourceEntry (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  sourceEntryCode (zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames)
    (endpoint_canonicalInitializedGlobals input endpoint endpointRelated).locals
    (HolFiniteMapExact.empty.updateList
      (functionsHOL FrontendStages.Declarations.functionDeclarations).reverse)

theorem endpoint_canonical_source_entry_rename (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    {endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated with code := (fpermCodeHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated).code)} = endpoint_canonicalRenamedSourceEntry input endpoint endpointRelated := by
  have table := rename_reverse_function_table FrontendStages.Declarations.globalStart
    FrontendStages.Declarations.globalNewStart FrontendStages.Declarations.functionDeclarations
  rw [GlobalsComputation.fpermDecs_eq_map] at table
  unfold endpoint_canonicalUnrenamedSourceEntry endpoint_canonicalRenamedSourceEntry
  rw [sourceEntryCode_code,sourceEntryCode_replace]
  exact congrArg (sourceEntryCode (zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames)
    (endpoint_canonicalInitializedGlobals input endpoint endpointRelated).locals) table

theorem endpoint_canonical_source_entry_rename_run (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) (fuel : Nat)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState {endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated with clock := fuel}
      (.call none FrontendStages.Declarations.globalStart []) = (result,post)) :
    evaluateHOLFiniteState {endpoint_canonicalRenamedSourceEntry input endpoint endpointRelated with clock := fuel}
      (.call none FrontendStages.Declarations.globalNewStart []) =
      (result,{post with code := (fpermCodeHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart post.code)}) := by
  have renamed := pan_rename_entry_run FrontendStages.Declarations.globalStart
    FrontendStages.Declarations.globalNewStart (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated) fuel result post run
  have transport := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    evaluateHOLFiniteState {state with clock := fuel}
      (.call none FrontendStages.Declarations.globalNewStart [])) (endpoint_canonical_source_entry_rename input endpoint endpointRelated)
  exact transport.symm.trans renamed

end InitECandidate.Runtime

-- Original module: CanonicalSourceEntryFields
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

/-- The generated initializer leaves the initial empty locals intact. -/

theorem endpoint_canonical_initialized_globals_locals (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    (endpoint_canonicalInitializedGlobals input endpoint endpointRelated).locals = HolFiniteMapExact.empty :=
  (Classical.choose_spec (endpoint_canonical_globals_ready input endpoint endpointRelated)).2.2.2.2.1

end InitECandidate.Runtime

-- Original module: CanonicalSourceFunctionsEvaluated
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The original function declaration evaluator installs precisely the
original-named source entry used by the quantitative native simulation. -/

theorem endpoint_canonical_source_functions_evaluate (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      (zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames)
      (fun address => Classical.propDecidable
        ((zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames).memaddrs address))
      FrontendStages.Declarations.functionDeclarations = some (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated) := by
  classical
  let state := zeroGlobalPost (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) baselineGlobalNames
  have structs : state.structs = [] := by
    dsimp only [state]
    rw [zero_global_post_frame]
    rfl
  have code : state.code = HolFiniteMapExact.empty := by
    dsimp only [state]
    rw [zero_global_post_frame]
    rfl
  have locals : state.locals = (endpoint_canonicalInitializedGlobals input endpoint endpointRelated).locals := by
    rw [endpoint_canonical_initialized_globals_locals]
    dsimp only [state]
    rw [zero_global_post_frame]
    rfl
  have checked : panDeclarationSetup state.structs state.eshapes
      FrontendStages.Declarations.functionDeclarations = true := by
    rw [structs,pan_function_setup_exceptions _ [] state.eshapes HolFiniteMapExact.empty baseline_source_functions_kind]
    exact baseline_source_functions_setup
  have evaluated := panDeclarationSetup_evaluates FrontendStages.Declarations.functionDeclarations state checked
  rw [baseline_source_functions_exceptions] at evaluated
  change evaluateDeclsHOLFinite state FrontendStages.Declarations.functionDeclarations =
    some {state with code := state.code.updateList (functionsHOL FrontendStages.Declarations.functionDeclarations)} at evaluated
  rw [code,function_table_reverse _ baseline_source_functions_distinct] at evaluated
  have post : {state with code := (HolFiniteMapExact.empty.updateList
      (functionsHOL FrontendStages.Declarations.functionDeclarations).reverse)} =
      endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated := by
    exact (source_entry_code_same_locals state _).symm.trans
      (congrArg (fun initialLocals => sourceEntryCode state initialLocals
        (HolFiniteMapExact.empty.updateList
          (functionsHOL FrontendStages.Declarations.functionDeclarations).reverse)) locals)
  rw [post] at evaluated
  exact evaluated

end InitECandidate.Runtime

-- Original module: CanonicalSourceExceptionsEvaluated
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact


theorem endpoint_canonical_source_exceptions_evaluate (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      FrontendStages.Declarations.exceptionDeclarations = some (endpoint_canonicalGlobalsSourceState input endpoint endpointRelated) := by
  classical
  have evaluated := panDeclarationSetup_evaluates FrontendStages.Declarations.exceptionDeclarations
    (sourceInitialState input) baseline_source_exceptions_setup
  rw [baseline_source_exceptions_functions] at evaluated
  have shapes : (endpoint_canonicalPanEntryState input endpoint endpointRelated).eshapes =
      HolFiniteMapExact.empty.updateList (exceptionsHOL FrontendStages.Declarations.exceptionDeclarations) := by
    change HolFiniteMapExact.empty.updateList (exceptionsHOL FrontendStages.pass2) = _
    rw [baseline_source_exceptions_table]
  have post : {(sourceInitialState input) with
      code := (sourceInitialState input).code.updateList []
      eshapes := (sourceInitialState input).eshapes.updateList
        (exceptionsHOL FrontendStages.Declarations.exceptionDeclarations)} = endpoint_canonicalGlobalsSourceState input endpoint endpointRelated := by
    unfold endpoint_canonicalGlobalsSourceState
    rw [shapes]
    rfl
  rw [post] at evaluated
  exact evaluated

end InitECandidate.Runtime

-- Original module: CanonicalSourceDeclarations
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact


theorem endpoint_canonical_source_declarations_evaluate (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      FrontendStages.pass1 = some (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated) := by
  classical
  have reordered : evaluateDeclsHOLFinite (sourceInitialState input)
      (resortDeclsHOL FrontendStages.pass1) = some (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated) := by
    change evaluateDeclsHOLFinite (sourceInitialState input)
      (resortDeclsHOL FrontendStages.Declarations.simplifieds) = _
    rw [FrontendStages.Declarations.sourceResort_eq]
    rw [Flapjack.evaluateDeclsHOLFinite_append,Flapjack.evaluateDeclsHOLFinite_append,endpoint_canonical_source_exceptions_evaluate]
    simp only [Option.bind_some]
    rw [endpoint_canonical_source_globals_evaluate]
    simp only [Option.bind_some]
    exact endpoint_canonical_source_functions_evaluate input endpoint endpointRelated
  rw [resortDeclsEvaluate (sourceInitialState input) FrontendStages.pass1 baseline_source_declaration_kinds] at reordered
  exact reordered

end InitECandidate.Runtime

-- Original module: CanonicalOriginalSourceEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The actual simplifier output initializes successfully on original memory. -/

theorem endpoint_canonical_simplified_declarations_evaluate (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ {sourceInitialState input with code := HolFiniteMapExact.empty}
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      (panSimpDeclsHOL sourceDeclarations) = some (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated) := by
  rw [FrontendStages.pass0_eq]
  exact endpoint_canonical_source_declarations_evaluate input endpoint endpointRelated

theorem endpoint_canonical_original_source_entry_exists (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    ∃ original, @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      sourceDeclarations = some original ∧
      PanSimp.stateRel original (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated)
        (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated).code := by
  classical
  obtain ⟨original,sourceRun⟩ := pan_simp_declarations_reflect sourceDeclarations (sourceInitialState input)
    (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
    HolFiniteMapExact.empty (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated) (endpoint_canonical_simplified_declarations_evaluate input endpoint endpointRelated)
  have codeRel : PanSimp.CodeRel (sourceInitialState input).code HolFiniteMapExact.empty := by
    refine ⟨fun _ _ => rfl,?_⟩
    intro name params body shape impossible
    cases impossible
  obtain ⟨code,simplifiedRun,related⟩ := PanSimp.evaluateDeclsCodeRel sourceDeclarations
    (sourceInitialState input) _ HolFiniteMapExact.empty original codeRel sourceRun
  have equal : endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated = {original with code := code} :=
    Option.some.inj ((endpoint_canonical_simplified_declarations_evaluate input endpoint endpointRelated).symm.trans simplifiedRun)
  have codeEq : (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated).code = code :=
    congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) equal
  refine ⟨original,sourceRun,?_⟩
  rw [codeEq]
  exact ⟨equal,related.1,related.2⟩

noncomputable def endpoint_canonicalOriginalSourceEntry (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    PanSemStateFiniteExact 64 Guest.HostMemory := Classical.choose (endpoint_canonical_original_source_entry_exists input endpoint endpointRelated)

theorem endpoint_canonical_original_declarations_evaluate (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      sourceDeclarations = some (endpoint_canonicalOriginalSourceEntry input endpoint endpointRelated) :=
  (Classical.choose_spec (endpoint_canonical_original_source_entry_exists input endpoint endpointRelated)).1

theorem endpoint_canonical_original_simplified_relation (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint) :
    PanSimp.stateRel (endpoint_canonicalOriginalSourceEntry input endpoint endpointRelated) (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated)
      (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated).code :=
  (Classical.choose_spec (endpoint_canonical_original_source_entry_exists input endpoint endpointRelated)).2

end InitECandidate.Runtime

-- Original module: BaselineGlobalsClock
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

/-- The actual generated global initializer contains no clock-consuming construct. -/

theorem endpoint_canonical_global_entry_clock (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (initialized : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initialRun : PanSemStateFiniteExact.evaluateHOLFiniteState
      {endpoint_canonicalPanEntryState input endpoint endpointRelated with locals := HolFiniteMapExact.empty}
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized))
    (fuel : Nat) (result : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {initialized with clock := fuel}
      (.call none FrontendStages.Declarations.globalNewStart []) = (result,post)) :
    ∃ final, PanSemStateFiniteExact.evaluateHOLFiniteState
      {endpoint_canonicalPanEntryState input endpoint endpointRelated with clock := fuel + 1}
      (.call none baselineCrepStart []) = (result,final) ∧ final.ffi = post.ffi := by
  have clock := baseline_globals_clock {endpoint_canonicalPanEntryState input endpoint endpointRelated with locals := HolFiniteMapExact.empty}
  rw [initialRun] at clock
  exact endpoint_canonical_global_entry_one_clock input endpoint endpointRelated initialized initialRun clock fuel result post run

end InitECandidate.Runtime

-- Original module: CanonicalGlobalNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- The concrete global wrapper adds one clock before native compilation. -/

theorem endpoint_canonical_global_return_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (initialized : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initialRun : PanSemStateFiniteExact.evaluateHOLFiniteState
      {endpoint_canonicalPanEntryState input endpoint endpointRelated with locals := HolFiniteMapExact.empty}
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized))
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({initialized with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wrapped,wrappedRun,ffi⟩ := endpoint_canonical_global_entry_clock input endpoint endpointRelated initialized
    initialRun fuel (some (.returned value)) post run
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_canonical_pan_return_native_affine input endpoint endpointRelated (fuel + 1) wrapped value wrappedRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

theorem endpoint_canonical_global_ffi_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (initialized : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initialRun : PanSemStateFiniteExact.evaluateHOLFiniteState
      {endpoint_canonicalPanEntryState input endpoint endpointRelated with locals := HolFiniteMapExact.empty}
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized))
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({initialized with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wrapped,wrappedRun,ffi⟩ := endpoint_canonical_global_entry_clock input endpoint endpointRelated initialized
    initialRun fuel (some (.finalFfi event)) post run
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_canonical_pan_ffi_native_affine input endpoint endpointRelated (fuel + 1) wrapped event wrappedRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

end InitECandidate.Runtime

-- Original module: CanonicalInitializedNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Native bound from the canonical initialized inner entry, with initialization discharged. -/

theorem endpoint_canonical_initialized_return_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({endpoint_canonicalInitializedGlobals input endpoint endpointRelated with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) :=
  endpoint_canonical_global_return_native_affine input endpoint endpointRelated (endpoint_canonicalInitializedGlobals input endpoint endpointRelated)
    (endpoint_canonical_globals_ready_run input endpoint endpointRelated) fuel post value run

theorem endpoint_canonical_initialized_ffi_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({endpoint_canonicalInitializedGlobals input endpoint endpointRelated with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) :=
  endpoint_canonical_global_ffi_native_affine input endpoint endpointRelated (endpoint_canonicalInitializedGlobals input endpoint endpointRelated)
    (endpoint_canonical_globals_ready_run input endpoint endpointRelated) fuel post event run

end InitECandidate.Runtime

-- Original module: CanonicalRenamedNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Actual renamed-source execution transfers to the installed native code. -/

theorem endpoint_canonical_renamed_return_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({endpoint_canonicalRenamedSourceEntry input endpoint endpointRelated with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨targetPost,_,_,compiledRun,related⟩ := pan_globals_same_clock
    (.call none FrontendStages.Declarations.globalNewStart [])
    {endpoint_canonicalRenamedSourceEntry input endpoint endpointRelated with clock := fuel} (some (.returned value))
    FrontendStages.Declarations.globalContext {endpoint_canonicalInitializedGlobals input endpoint endpointRelated with clock := fuel} post
    ⟨endpoint_canonical_globals_function_relation input endpoint endpointRelated fuel,run,by simp⟩
  have call : compileProgExactHOL FrontendStages.Declarations.globalContext
      (.call none FrontendStages.Declarations.globalNewStart []) =
      .call none FrontendStages.Declarations.globalNewStart [] := by
    simp [compileProgExactHOL,compileExpExactHOLList]
  rw [call] at compiledRun
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_canonical_initialized_return_native_affine input endpoint endpointRelated fuel targetPost value compiledRun
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,ffi,_⟩ := related
  rw [← ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

theorem endpoint_canonical_renamed_ffi_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({endpoint_canonicalRenamedSourceEntry input endpoint endpointRelated with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨targetPost,_,_,compiledRun,related⟩ := pan_globals_same_clock
    (.call none FrontendStages.Declarations.globalNewStart [])
    {endpoint_canonicalRenamedSourceEntry input endpoint endpointRelated with clock := fuel} (some (.finalFfi event))
    FrontendStages.Declarations.globalContext {endpoint_canonicalInitializedGlobals input endpoint endpointRelated with clock := fuel} post
    ⟨endpoint_canonical_globals_function_relation input endpoint endpointRelated fuel,run,by simp⟩
  have call : compileProgExactHOL FrontendStages.Declarations.globalContext
      (.call none FrontendStages.Declarations.globalNewStart []) =
      .call none FrontendStages.Declarations.globalNewStart [] := by
    simp [compileProgExactHOL,compileExpExactHOLList]
  rw [call] at compiledRun
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_canonical_initialized_ffi_native_affine input endpoint endpointRelated fuel targetPost event compiledRun
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,ffi,_⟩ := related
  rw [← ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

end InitECandidate.Runtime

-- Original module: CanonicalUnrenamedNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Native bound from an original-named source main run, retaining its clock. -/

theorem endpoint_canonical_unrenamed_return_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  have renamed := endpoint_canonical_source_entry_rename_run input endpoint endpointRelated fuel (some (.returned value)) post run
  exact endpoint_canonical_renamed_return_native_affine input endpoint endpointRelated fuel
    {post with code := (fpermCodeHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart post.code)} value renamed

theorem endpoint_canonical_unrenamed_ffi_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  have renamed := endpoint_canonical_source_entry_rename_run input endpoint endpointRelated fuel (some (.finalFfi event)) post run
  exact endpoint_canonical_renamed_ffi_native_affine input endpoint endpointRelated fuel
    {post with code := (fpermCodeHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart post.code)} event renamed

end InitECandidate.Runtime

-- Original module: CanonicalOriginalNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Original challenge-source main execution gives an actual installed native
run with a bounded clock, preserving the original resource-limit alternative. -/

theorem endpoint_canonical_original_return_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({endpoint_canonicalOriginalSourceEntry input endpoint endpointRelated with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨simplifiedPost,simplifiedRun,ffi,clock,related⟩ := pan_simp_entry_same_clock
    (endpoint_canonicalOriginalSourceEntry input endpoint endpointRelated) (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated)
    FrontendStages.Declarations.globalStart fuel (endpoint_canonical_original_simplified_relation input endpoint endpointRelated)
    (some (.returned value)) post run (by simp)
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_canonical_unrenamed_return_native_affine input endpoint endpointRelated fuel simplifiedPost value simplifiedRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

theorem endpoint_canonical_original_ffi_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (endpointRelated : targetStateRel Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget InitE.installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({endpoint_canonicalOriginalSourceEntry input endpoint endpointRelated with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨simplifiedPost,simplifiedRun,ffi,clock,related⟩ := pan_simp_entry_same_clock
    (endpoint_canonicalOriginalSourceEntry input endpoint endpointRelated) (endpoint_canonicalUnrenamedSourceEntry input endpoint endpointRelated)
    FrontendStages.Declarations.globalStart fuel (endpoint_canonical_original_simplified_relation input endpoint endpointRelated)
    (some (.finalFfi event)) post run (by simp)
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_canonical_unrenamed_ffi_native_affine input endpoint endpointRelated fuel simplifiedPost event simplifiedRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.endpoint_EntrySourceRegisters
#print axioms InitECandidate.Runtime.endpoint_canonicalPanDeclarationState
#print axioms InitECandidate.Runtime.endpoint_entry_selected_fields
#print axioms InitECandidate.Runtime.endpoint_entry_frontend_ffi
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_entry_ffi
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_declaration_ffi
#print axioms InitECandidate.Runtime.endpoint_entry_frontend_heap_register
#print axioms InitECandidate.Runtime.endpoint_canonical_heap_base_register
#print axioms InitECandidate.Runtime.endpoint_canonical_heap_base_source
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_declaration_base
#print axioms InitECandidate.Runtime.endpoint_entry_fullMakeInit
#print axioms InitECandidate.Runtime.endpoint_entry_lab_pointers
#print axioms InitECandidate.Runtime.endpoint_entry_frontend_domain
#print axioms InitECandidate.Runtime.endpoint_entry_frontend_heap_length
#print axioms InitECandidate.Runtime.endpoint_entry_frontend_heap_memory
#print axioms InitECandidate.Runtime.endpoint_canonical_heap_length_store
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_heap_top
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_memory_domain
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_memory_domain_split
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_memory_agreement
#print axioms InitECandidate.Runtime.endpoint_entry_frontend_endian_shared
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_endian
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_shared_domain
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_source_top
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_source_domain
#print axioms InitECandidate.Runtime.endpoint_entry_frontend_clock_zero
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_declaration_clock
#print axioms InitECandidate.Runtime.endpoint_canonical_pan_top_outside
#print axioms InitECandidate.Runtime.endpoint_canonicalGlobalsSourceState
#print axioms InitECandidate.Runtime.endpoint_canonical_globals_initial_relation
#print axioms InitECandidate.Runtime.endpoint_canonical_globals_initialize
#print axioms InitECandidate.Runtime.endpoint_canonical_source_globals_evaluate
#print axioms InitECandidate.Runtime.endpoint_canonical_globals_ready
#print axioms InitECandidate.Runtime.endpoint_canonicalInitializedGlobals
#print axioms InitECandidate.Runtime.endpoint_canonical_globals_ready_run
#print axioms InitECandidate.Runtime.endpoint_canonical_globals_ready_relation
#print axioms InitECandidate.Runtime.endpoint_baseline_pan_generated_main
#print axioms InitECandidate.Runtime.endpoint_baseline_pan_renamed_main
#print axioms InitECandidate.Runtime.endpoint_canonical_global_entry_one_clock
#print axioms InitECandidate.Runtime.endpoint_canonical_compiled_function_lookup
#print axioms InitECandidate.Runtime.endpoint_canonical_globals_ready_code
#print axioms InitECandidate.Runtime.endpoint_canonicalRenamedSourceEntry
#print axioms InitECandidate.Runtime.endpoint_canonical_globals_function_relation
#print axioms InitECandidate.Runtime.endpoint_canonicalUnrenamedSourceEntry
#print axioms InitECandidate.Runtime.endpoint_canonical_source_entry_rename
#print axioms InitECandidate.Runtime.endpoint_canonical_source_entry_rename_run
#print axioms InitECandidate.Runtime.endpoint_canonical_initialized_globals_locals
#print axioms InitECandidate.Runtime.endpoint_canonical_source_functions_evaluate
#print axioms InitECandidate.Runtime.endpoint_canonical_source_exceptions_evaluate
#print axioms InitECandidate.Runtime.endpoint_canonical_source_declarations_evaluate
#print axioms InitECandidate.Runtime.endpoint_canonical_simplified_declarations_evaluate
#print axioms InitECandidate.Runtime.endpoint_canonical_original_source_entry_exists
#print axioms InitECandidate.Runtime.endpoint_canonicalOriginalSourceEntry
#print axioms InitECandidate.Runtime.endpoint_canonical_original_declarations_evaluate
#print axioms InitECandidate.Runtime.endpoint_canonical_original_simplified_relation
#print axioms InitECandidate.Runtime.endpoint_canonical_global_entry_clock
#print axioms InitECandidate.Runtime.endpoint_canonical_global_return_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_global_ffi_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_initialized_return_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_initialized_ffi_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_renamed_return_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_renamed_ffi_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_unrenamed_return_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_unrenamed_ffi_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_original_return_native_affine
#print axioms InitECandidate.Runtime.endpoint_canonical_original_ffi_native_affine
