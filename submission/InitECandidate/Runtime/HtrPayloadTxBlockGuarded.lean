import InitECandidate.Runtime.HtrPayloadTxBlockBound
import InitECandidate.Runtime.HtrPayloadTxLoopGuarded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Array/workspace separation is required only for a nonempty transaction
list; zero-count arrays can be null and the actual loop performs no reads. -/
theorem runBounded_htrPayload_tx_block_guarded (pointer accelerator zeroHashes chunk array roots heap input inputLength count : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count.toNat * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (pointerFits : count ≠ 0 → pointer.toNat + 64 ≤ array.toNat)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) (chunks : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (budget : rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2) ≤ state.clock) :
    RunBounded state htrPayloadTxBlock (rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) := by
  have loop := htrPayload_tx_loop_ranked_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits rank state code valid (by omega)
  have loopBound : RunBounded state (.while htrPayloadTxCondition htrPayloadTxStep)
      (rank * (htrPbytesBodyCost + 2)) := ⟨loop.1,loop.2.1,loop.2.2.1⟩
  exact RunBounded.seq loopBound budget (by
    intro next normal nextCode remaining
    have nextLoop := loop
    rw [normal] at nextLoop
    obtain ⟨nextRank,nextValid,_,_⟩ := nextLoop.2.2.2 rfl
    have atChunks := (htrPayload_tx_loop_local_frame state next (ofString "ch") (by decide) normal).trans chunksLocal
    have hashed := runBounded_htrPayload_tx_hash next roots count chunks heap nextValid.rootsLocal
      nextValid.countLocal atChunks nextValid.heapGlobal countBound heapFits (nextCode.trans code) (by omega)
    have combined := RunBounded.seq (tail := htrPayloadTxRelease) (b := 1) hashed (by omega) (by
      intro released releaseNormal releaseCode releaseBudget
      apply RunBounded.ofProg _ (releaseCode.trans (nextCode.trans code)) releaseBudget
      exact ProgBounded.call vmBound_heap_release _ _)
    simpa only [Nat.add_assoc] using combined)

#print axioms runBounded_htrPayload_tx_block_guarded
end InitECandidate.Runtime
