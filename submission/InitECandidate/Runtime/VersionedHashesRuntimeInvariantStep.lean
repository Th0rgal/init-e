import InitECandidate.Runtime.VersionedHashesRuntimeInvariant
import InitECandidate.Runtime.VersionedHashesUniformSourceStepHeapGrowth
import InitECandidate.Runtime.VersionedHashesSourceStepOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem versioned_hashes_runtime_invariant_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : VersionedHashesRuntimeInvariant state count array vh input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (active : 0 < versionedHashesRank count state)
    (budget : transactionWrapperCallCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    Nonempty (VersionedHashesRuntimeInvariant post count array vh input inputLength scratch frame ceiling) ∧
      versionedHashesRank count post < versionedHashesRank count state := by
  have rank : versionedHashesRank count state = count.toNat - valid.locals.index.toNat := by
    simp [versionedHashesRank,valid.locals.indexLocal]
  have inside : valid.locals.index.toNat < count.toNat := by rw [rank] at active; omega
  obtain ⟨pointer,length,slice⟩ := valid.slices valid.locals.index inside
  have lengthBound := slice.length_bound state array valid.locals.index pointer length input inputLength
  have frameSpace : valid.heap.toNat + transactionHeapWorkspace inputLength.toNat ≤ frame.toNat := by
    have reserve := valid.frameReserve; omega
  have capSpace : valid.heap.toNat + transactionHeapWorkspace inputLength.toNat ≤ 33806089496 := by
    have reserve := valid.capReserve; omega
  have workspaceLower : 400 + inputLength.toNat * 16 ≤ transactionHeapWorkspace inputLength.toNat := by
    dsimp only [transactionHeapWorkspace,transactionHeapGrowth]; omega
  have heapSmall : valid.heap.toNat + 400 ≤ 33806089496 := by omega
  have arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat := valid.arrayBeforeHeap.trans (by omega)
  have inputBelow : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat) :=
    Or.inl (valid.inputBeforeHeap.trans (by omega))
  obtain ⟨nextHeap,binding,lower,upper,heapBound,aligned,scratchFinal,frameFinal⟩ := versioned_hashes_uniform_source_step_heap_growth state post
    array valid.locals.index input inputLength vh valid.locals.cursor valid.locals.arrayLocal valid.locals.indexLocal valid.locals.vhLocal
    valid.locals.cursorLocal pointer length scratch frame valid.heap ceiling inputLimit slice inputBound limitBound valid.scratchGlobal valid.frameGlobal
    valid.locals.code orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal heapSmall countLimit valid.heapArena inputBelow valid.inputBeforeHeap
    frameSpace valid.heapAligned budget (by omega) array count input inputLength valid.slices arrayBelow valid.arrayBeforeHeap run
  have cost := transaction_wrapper_call_cost_mono length.toNat inputLength.toNat lengthBound
  have workspace := transaction_heap_workspace_mono length.toNat inputLength.toNat lengthBound
  have nestedReserve : valid.heap.toNat + transactionHeapWorkspace length.toNat ≤ frame.toNat := by omega
  rw [transaction_heap_workspace_exact] at nestedReserve
  have slices := versioned_hashes_source_step_normal_outer_prefix state post array valid.locals.index input inputLength vh valid.locals.cursor
    valid.locals.arrayLocal valid.locals.indexLocal valid.locals.vhLocal valid.locals.cursorLocal pointer length scratch frame valid.heap ceiling inputLimit
    slice inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.locals.code orderedFrame framePositive scratchBelow valid.arena
    valid.heapGlobal heapSmall countLimit valid.heapArena inputBelow valid.inputBeforeHeap
    (by simpa only [Nat.add_assoc] using nestedReserve) valid.heapAligned (cost.trans budget)
    (by have product := Nat.mul_le_mul_right 16 lengthBound; omega) array count input inputLength valid.slices arrayBelow valid.arrayBeforeHeap run
  obtain ⟨⟨locals⟩,decreases⟩ := versioned_hashes_locals_invariant_step state post count array vh valid.locals active run
  have metadata := evaluateHOLFiniteState_metadata state versionedHashesStep
  rw [run] at metadata
  have remaining : versionedHashesRank count post ≤ versionedHashesRank count state - 1 := by omega
  have product := Nat.mul_le_mul_right (transactionHeapGrowth inputLength.toNat) remaining
  have nextFrame := transaction_heap_reserve_step valid.heap.toNat nextHeap.toNat (versionedHashesRank count state)
    inputLength.toNat frame.toNat active upper valid.frameReserve
  have nextCap := transaction_heap_reserve_step valid.heap.toNat nextHeap.toNat (versionedHashesRank count state)
    inputLength.toNat 33806089496 active upper valid.capReserve
  refine ⟨⟨⟨locals,slices,nextHeap,binding,scratchFinal,frameFinal,aligned,heapBound,?_,?_,
    valid.inputBeforeHeap.trans lower,valid.arrayBeforeHeap.trans lower,?_,?_⟩⟩,decreases⟩
  · intro address low high; rw [metadata.2.1]; exact valid.arena address low high
  · intro address low high; rw [metadata.2.1]; exact valid.heapArena address (lower.trans low) high
  · omega
  · omega

#print axioms versioned_hashes_runtime_invariant_step
end InitECandidate.Runtime
