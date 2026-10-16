import InitECandidate.Runtime.CanonicalSourceState
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Compiler.Backend

/-- Reserving the globals tail does not overlap any ordinary source word. -/
theorem baseline_globals_disjoint (address : BitVec 64)
    (ordinary : ordinaryDomain address) :
    ¬ StackRemove.addresses (BitVec.ofNat 64 heapEnd) globalsWords address := by
  rw [ordinaryDomain, StackRemove.mem_addresses] at ordinary
  rw [StackRemove.mem_addresses]
  obtain ⟨i,hi,eqi⟩ := ordinary
  rintro ⟨j,hj,eqj⟩
  have equal := congrArg BitVec.toNat (eqi.symm.trans eqj)
  norm_num [sourceBase,heapEnd,stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,
    StackRemove.bytesInWord,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat] at hi hj equal
  omega

theorem baseline_globals_top_aligned :
    panGlobalsByteAlignedHOL (BitVec.ofNat 64 stackStart) := by
  unfold panGlobalsByteAlignedHOL
  decide_cbv

theorem baseline_globals_size_fits :
    (panBytesInWord 64).toNat * globalsWords < 2 ^ 64 := by decide_cbv

/-- The expanded source domain excludes its one-past-the-end pointer. -/
theorem canonical_pan_top_outside (input : Guest.InputBlob) :
    ¬ (canonicalPanDeclarationState input).memaddrs
      (canonicalPanDeclarationState input).topAddr := by
  rw [canonical_pan_memory_domain,canonical_pan_heap_top]
  have top : (BitVec.ofNat 64 sourceBase) + panBytesInWord 64 *
      BitVec.ofNat 64 ((stackStart-sourceBase)/8) = BitVec.ofNat 64 stackStart := by decide_cbv
  rw [← top]
  exact PanGlobalsCompileTopSemanticsDecls.topNotInAddresses (Or.inr rfl) _ _ (by decide)

#print axioms baseline_globals_disjoint
#print axioms baseline_globals_top_aligned
#print axioms baseline_globals_size_fits
#print axioms canonical_pan_top_outside
end InitECandidate.Runtime
