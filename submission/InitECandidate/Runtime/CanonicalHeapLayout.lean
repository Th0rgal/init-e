import InitECandidate.Runtime.BaselineFrontendLayout
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend Classical
open Flapjack.Pancake.Proofs.PanToTarget

noncomputable def baselineHeapLength : BitVec 64 :=
  BitVec.ofNat 64 (StackRemove.Proofs.InitLimits.getStackHeapLimit entryHeapLimit
    (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 stackStart,BitVec.ofNat 64 ramEnd)).2 * StackRemove.bytesInWord 64

theorem baseline_heap_top : (BitVec.ofNat 64 sourceBase) + 2 * baselineHeapLength = BitVec.ofNat 64 stackStart := by decide_cbv

theorem baseline_heap_word_count :
    ((BitVec.ofNat 64 stackStart) + -1 * BitVec.ofNat 64 sourceBase).toNat / 8 =
      (stackStart - sourceBase) / 8 := by decide_cbv

theorem baseline_globals_tail :
    (BitVec.ofNat 64 sourceBase) + StackRemove.bytesInWord 64 * BitVec.ofNat 64 ((stackStart-sourceBase)/8) -
      BitVec.ofNat 64 (globalsWords * 64 / 8) = BitVec.ofNat 64 heapEnd := by decide_cbv

theorem canonical_heap_length_store (input : Guest.InputBlob) :
    (entryFrontendState (canonicalRuntimeEntry input)).store.lookup .heapLength = some (.word baselineHeapLength) :=
  entry_frontend_heap_length _ (canonical_source_registers input)

theorem canonical_pan_heap_top (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).topAddr = BitVec.ofNat 64 stackStart := by
  obtain ⟨capacity,_,_,_,_,_,_,_,length,top,_⟩ := canonical_loop_related input
  have stored := canonical_heap_length_store input
  have equal := WordLocW.word.inj (Option.some.inj (length.symm.trans stored))
  rw [equal] at top
  change (canonicalPanDeclarationState input).topAddr = canonicalHeapBase input + 2 * baselineHeapLength at top
  rw [canonical_heap_base_source,baseline_heap_top] at top
  exact top

theorem canonical_pan_memory_domain (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).memaddrs =
      StackRemove.addresses (BitVec.ofNat 64 sourceBase) ((stackStart-sourceBase)/8) := by
  funext address
  change ((entryFrontendState (canonicalRuntimeEntry input)).mdomain address = true) = _
  rw [entry_frontend_domain _ (canonical_source_registers input),baseline_heap_word_count]
  simp only [decide_eq_true_eq]

theorem canonical_pan_memory_domain_split (input : Guest.InputBlob) :
    (canonicalPanDeclarationState input).memaddrs = fun address =>
      ordinaryDomain address ∨ StackRemove.addresses (BitVec.ofNat 64 heapEnd) globalsWords address := by
  rw [canonical_pan_memory_domain]
  have split := addressesSplitGlobals (width := 64) (Or.inr rfl) (BitVec.ofNat 64 sourceBase)
    ((stackStart-sourceBase)/8) globalsWords (by decide)
  rw [baseline_globals_tail] at split
  exact split.symm

theorem canonical_pan_memory_agreement (input : Guest.InputBlob) (address : BitVec 64)
    (valid : (sourceInitialState input).memaddrs address) :
    (canonicalPanDeclarationState input).memory address = (sourceInitialState input).memory address := by
  have whole : (canonicalPanDeclarationState input).memaddrs address := by
    rw [canonical_pan_memory_domain_split]
    exact Or.inl valid
  have actual := entry_frontend_heap_memory (canonicalRuntimeEntry input) address whole
  have source := (canonicalRuntimeEntry input).memoryAgreement address valid
  change wlocWlabHOL ((entryFrontendState (canonicalRuntimeEntry input)).memory address) = _
  rw [actual,source]
  rfl

#print axioms baseline_heap_top
#print axioms canonical_heap_length_store
#print axioms canonical_pan_heap_top
#print axioms canonical_pan_memory_domain
#print axioms canonical_pan_memory_domain_split
#print axioms canonical_pan_memory_agreement
end InitECandidate.Runtime
