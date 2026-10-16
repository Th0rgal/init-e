import InitECandidate.Runtime.BaselineHeapLayoutFacts
import InitECandidate.Runtime.SelectedFullInitialization
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend Classical
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Pancake.Proofs.PanToTarget

/-- The actual selected initializer is the full initializer's exact result. -/
theorem entry_fullMakeInit {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    fullMakeInit baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf entryHeapLimit entrySp
      riscvConfig.addrOffset InitECandidate.bitmaps BackendStages.Native.stack
      (LabToTarget.baselineLabState input entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain)
      entrySaveRegs 0 (entryStackOracle entry.cfg) =
      (entryStackState entry.cfg entry.source,some entry.source) := by
  rw [fullMakeInit_eq]
  simp only [entry.selection,StackRemove.Proofs.InitMake.makeInitAny]
  rfl

theorem entry_lab_pointers {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (regs : EntrySourceRegisters entry) :
    let lab := LabToTarget.baselineLabState input entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain
    lab.regs lab.lenReg = .word (BitVec.ofNat 64 sourceBase) ∧
    lab.regs lab.ptr2Reg = .word (BitVec.ofNat 64 stackStart) ∧
    lab.regs lab.len2Reg = .word (BitVec.ofNat 64 ramEnd) := by
  exact ⟨congrArg WordLocW.word regs.1,congrArg WordLocW.word regs.2.1,congrArg WordLocW.word regs.2.2⟩

theorem entry_frontend_domain {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (regs : EntrySourceRegisters entry) (address : BitVec 64) :
    (entryFrontendState entry).mdomain address =
      decide (StackRemove.addresses (BitVec.ofNat 64 sourceBase)
        (((BitVec.ofNat 64 stackStart) + -1 * BitVec.ofNat 64 sourceBase).toNat / 8) address) := by
  have ptr := entry_lab_pointers entry regs
  exact panToTargetWordInitMdomain (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList BackendStages.Native.programs0) (worac := entryWordOracle entry.cfg)
    (BitVec.ofNat 64 sourceBase) (BitVec.ofNat 64 stackStart) (BitVec.ofNat 64 ramEnd)
    entry.stackAssumptions (entry_fullMakeInit entry) ptr.1 ptr.2.1 ptr.2.2
    baseline_heap_low baseline_heap_high baseline_heap_fits baseline_heap_limit_fits baseline_heap_aligned address

theorem entry_frontend_heap_length {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (regs : EntrySourceRegisters entry) :
    (entryFrontendState entry).store.lookup .heapLength = some (.word
      (BitVec.ofNat 64 (StackRemove.Proofs.InitLimits.getStackHeapLimit entryHeapLimit
        (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 stackStart,BitVec.ofNat 64 ramEnd)).2 * StackRemove.bytesInWord 64)) := by
  have ptr := entry_lab_pointers entry regs
  obtain ⟨base,found,current,length⟩ := panToTargetWordInitStore (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList BackendStages.Native.programs0) (worac := entryWordOracle entry.cfg)
    entry.stackAssumptions (entry_fullMakeInit entry)
  rw [readPointers_s2 entry.stackAssumptions ptr.1 ptr.2.1 ptr.2.2] at length
  exact length

theorem entry_frontend_heap_memory {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (address : BitVec 64) (valid : (entryFrontendState entry).mdomain address = true) :
    (entryFrontendState entry).memory address = entry.memory address := by
  have fields := panToTargetWordInitMemory (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList BackendStages.Native.programs0) (worac := entryWordOracle entry.cfg)
    entry.stackAssumptions (entry_fullMakeInit entry)
  exact fields.2.2.2 address valid

#print axioms entry_fullMakeInit
#print axioms entry_lab_pointers
#print axioms entry_frontend_domain
#print axioms entry_frontend_heap_length
#print axioms entry_frontend_heap_memory
end InitECandidate.Runtime
