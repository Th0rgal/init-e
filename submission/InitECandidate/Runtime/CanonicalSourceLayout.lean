import InitECandidate.Runtime.CanonicalHeapLayout
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

theorem entry_frontend_endian_shared {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    (entryFrontendState entry).be = false ∧
    (entryFrontendState entry).shMdomain =
      (LabToTarget.baselineLabState input entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain).sharedMemDomain := by
  have fields := panToTargetWordInitMemory (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList BackendStages.Native.programs0) (worac := entryWordOracle entry.cfg)
    entry.stackAssumptions (entry_fullMakeInit entry)
  exact ⟨fields.2.1,fields.2.2.1⟩

theorem canonical_pan_endian (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).be = (sourceInitialState input).be :=
  (entry_frontend_endian_shared (canonicalRuntimeEntry input)).1

theorem canonical_pan_shared_domain (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).shMemaddrs = (sourceInitialState input).shMemaddrs := by
  funext address
  change ((entryFrontendState (canonicalRuntimeEntry input)).shMdomain address = true) = _
  rw [congrFun (entry_frontend_endian_shared (canonicalRuntimeEntry input)).2 address]
  change (((canonicalRuntimeEntry input).sharedDomain address && holByteAligned address) = true) = _
  simpa only [Bool.and_eq_true] using (congrFun (canonicalRuntimeEntry input).sharedAgreement address).symm

theorem source_top_with_globals (input : Guest.InputBlob) :
    (sourceInitialState input).topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsWords =
      BitVec.ofNat 64 stackStart := by
  change (BitVec.ofNat 64 heapEnd) + panBytesInWord 64 * BitVec.ofNat 64 globalsWords = _
  decide_cbv

theorem canonical_pan_source_top (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).topAddr =
      (sourceInitialState input).topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsWords := by
  rw [canonical_pan_heap_top,source_top_with_globals]

theorem canonical_pan_source_domain (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).memaddrs = fun address =>
      (sourceInitialState input).memaddrs address ∨
        StackRemove.addresses (sourceInitialState input).topAddr globalsWords address :=
  canonical_pan_memory_domain_split input

#print axioms entry_frontend_endian_shared
#print axioms canonical_pan_endian
#print axioms canonical_pan_shared_domain
#print axioms canonical_pan_source_top
#print axioms canonical_pan_source_domain
end InitECandidate.Runtime
