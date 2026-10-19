import InitECandidate.Runtime.HtrPayloadPostWithdrawalMemory
import InitECandidate.Runtime.HtrPayloadWithdrawalSuffixBound
import InitECandidate.Runtime.ListHashLayoutHeapRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual withdrawal loop, root hash and inner release compose with the
remaining payload hashes, retaining both request metadata and watched memory. -/
theorem htrPayload_withdrawal_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk array roots heap count chunks mark outerMark payload requests length raw out watched : BitVec 64)
    (rank : Nat) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (locals : PayloadFinalLocals state payload raw chunks out)
    (outerLocal : state.locals.lookup (ofString "mark") = some (.val (.word outerMark)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (markAligned : mark.toNat % 8 = 0) (markBound : mark.toNat ≤ 33806089496) (watchedMark : watched.toNat < mark.toNat)
    (lengthBound : length.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat) (watchedChunks : watched.toNat < chunks.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (payloadRoots : payload.toNat + 72 < roots.toNat) (watchedRoots : watched.toNat < roots.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (shaPayload : sha.toNat + 64 ≤ payload.toNat)
    (valid : HtrPayloadWithdrawalState array roots heap count state rank)
    (entry : RlpSliceEntry state payload (4#64) requests length)
    (budget : (rank * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 28) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [evaluate_htrPayload_withdrawal_block_source] at run
  obtain ⟨next,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  let blockCost := rank * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)
  have enough : blockCost ≤ state.clock := (Nat.le_add_right blockCost htrPayloadPostWithdrawalCost).trans budget
  have frame := htrPayload_withdrawal_block_normal_memory state next sha accelerator zeroHashes chunk array roots count chunks heap mark watched rank
    valid rootsAligned rootsFits watchedRoots locals.2.2.1 markLocal layout.atSha layout.atAccel layout.atChunk layout.atZero layout.atHeap
    chunksAligned chunksFits watchedChunks countBound layout.chunkAligned layout.chunkFits layout.chunkOutside
    layout.heapAligned layout.heapFits layout.heapBefore layout.accelAligned layout.accelFits layout.shaFits
    layout.accelOutside layout.shaOutside layout.code enough normal
  have entryKept := htrPayload_withdrawal_block_preserves_requests state next sha accelerator zeroHashes chunk
    array roots heap count chunks mark payload requests length rank locals.2.2.1 markLocal chunksAligned chunksFits payloadChunks
    layout.chunkAligned chunkPayload layout.atChunk countBound rootsAligned rootsFits layout.heapAligned layout.heapFits
    payloadRoots payloadHeap layout.accelAligned accelPayload shaPayload layout.code valid layout.atSha layout.atAccel layout.atZero entry enough normal
  have globals := htrPayload_withdrawal_block_normal_globals state next mark markLocal layout.code normal
  have metadata := evaluateHOLFiniteState_metadata state htrPayloadWithdrawalBlock
  have bounded := runBounded_htrPayload_withdrawal_block array roots heap count countBound layout.heapFits state rank chunks
    layout.code valid locals.2.2.1 enough
  unfold RunBounded at bounded
  rw [normal] at metadata bounded
  have nextLayout := layout.after_heap_restore globals metadata.1 markAligned markBound watchedMark
  have keep (key : MlS) (different : key ≠ ofString "i") : next.locals.lookup key = state.locals.lookup key :=
    htrPayload_withdrawal_block_local_frame state next key different normal
  have spent : state.clock ≤ next.clock + blockCost := bounded.1
  have remaining : htrPayloadPostWithdrawalCost ≤ next.clock := by
    change blockCost + htrPayloadPostWithdrawalCost ≤ state.clock at budget
    generalize blockCost = bc at budget spent
    generalize htrPayloadPostWithdrawalCost = cost at budget ⊢
    omega
  have suffix := payload_post_withdrawal_suffix_memory next post sha accelerator zeroHashes chunk mark payload raw chunks out outerMark
    requests length watched value nextLayout
    ⟨(keep _ (by decide)).trans locals.1,(keep _ (by decide)).trans locals.2.1,
      (keep _ (by decide)).trans locals.2.2.1,(keep _ (by decide)).trans locals.2.2.2⟩
    ((keep _ (by decide)).trans outerLocal) entryKept lengthBound chunksAligned chunksFits payloadChunks watchedChunks remaining tail
  exact suffix.trans frame

#print axioms htrPayload_withdrawal_suffix_returned_memory
end InitECandidate.Runtime
