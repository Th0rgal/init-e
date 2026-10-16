import InitECandidate.Runtime.SelectedFullInitializerFields
import InitECandidate.Runtime.CanonicalPanDeclarations
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend

/-- Exact fields of the selected initialized state, derived solely from its
original full initialization assumptions and successful optional selection. -/
theorem entry_selected_fields {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    entry.source.ffi = sourceFfi input ∧
      entry.source.store.lookup .currHeap = some (.word
        (entry.asm.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2))) := by
  exact StackRemove.selected_fields_of_full_initialization baselineCompilerConfig.stackConf
    baselineCompilerConfig.dataConf entryHeapLimit entrySp
    Compiler.Encoders.RiscV.Target.riscvConfig.addrOffset InitECandidate.bitmaps BackendStages.Native.stack
    (LabToTarget.baselineLabState input entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain)
    entrySaveRegs 0 (entryStackOracle entry.cfg) entry.stackAssumptions entry.source entry.selection

theorem entry_frontend_ffi {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    (entryFrontendState entry).ffi = sourceFfi input := by
  change entry.source.ffi = sourceFfi input
  exact (entry_selected_fields entry).1

theorem canonical_pan_entry_ffi (input : Guest.InputBlob) :
    (canonicalPanEntryState input).ffi = sourceFfi input :=
  entry_frontend_ffi (canonicalRuntimeEntry input)

theorem canonical_pan_declaration_ffi (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).ffi = sourceFfi input :=
  canonical_pan_entry_ffi input

theorem entry_frontend_heap_register {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    (entryFrontendState entry).store.lookup .currHeap = some (.word
      (entry.asm.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2))) := by
  change (entry.source.store.eraseEq .handler).lookup .currHeap = _
  simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using (entry_selected_fields entry).2

theorem canonical_heap_base_register (input : Guest.InputBlob) :
    canonicalHeapBase input = (canonicalRuntimeEntry input).asm.regs
      (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2) := by
  obtain ⟨capacity,_,_,_,_,_,_,heap,_⟩ := canonical_loop_related input
  have installed := entry_frontend_heap_register (canonicalRuntimeEntry input)
  have equal := Option.some.inj (heap.symm.trans installed)
  exact WordLocW.word.inj equal

#print axioms entry_frontend_heap_register
#print axioms canonical_heap_base_register
#print axioms entry_selected_fields
#print axioms entry_frontend_ffi
#print axioms canonical_pan_entry_ffi
#print axioms canonical_pan_declaration_ffi
end InitECandidate.Runtime
