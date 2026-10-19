import InitECandidate.Runtime.HtrPayloadTxHashBound
import InitECandidate.Runtime.VmFn_heap_release
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrPayloadTxRelease : ProgHOL 64 :=
  .call (some (none,none)) (ofString "heap_release") [.var .local (ofString "m2")]

def htrPayloadTxBlock : ProgHOL 64 :=
  .seq (.while htrPayloadTxCondition htrPayloadTxStep) (.seq htrPayloadTxHashCall htrPayloadTxRelease)

theorem source_htrPayload_tx_release : htrPayloadAt 23 =
    .seq htrPayloadTxRelease (htrPayloadAt 24) := by rfl

theorem evaluate_htrPayload_tx_block_source {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (htrPayloadAt 21) =
      evaluateHOLFiniteState state (.seq htrPayloadTxBlock (htrPayloadAt 24)) := by
  rw [source_htrPayload_transactions,source_htrPayload_tx_hash,source_htrPayload_tx_release]
  unfold htrPayloadTxBlock
  rw [evaluate_seq_assoc]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_seq_line780]
  cases loop : evaluateHOLFiniteState state (.while htrPayloadTxCondition htrPayloadTxStep) with
  | mk result post =>
    cases result with
    | none => exact (evaluate_seq_assoc post htrPayloadTxHashCall htrPayloadTxRelease (htrPayloadAt 24)).symm
    | some result => rfl

theorem runBounded_htrPayload_tx_block (pointer accelerator zeroHashes chunk array roots heap input inputLength count : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count.toNat * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) (chunks : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (budget : rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2) ≤ state.clock) :
    RunBounded state htrPayloadTxBlock (rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) := by
  have loop := htrPayload_tx_loop_ranked pointer accelerator zeroHashes chunk array roots heap input inputLength count
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

#print axioms evaluate_htrPayload_tx_block_source
#print axioms source_htrPayload_tx_release
#print axioms runBounded_htrPayload_tx_block
end InitECandidate.Runtime
