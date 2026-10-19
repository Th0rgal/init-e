import InitECandidate.Runtime.HtrPayloadWithdrawalHashMemory
import InitECandidate.Runtime.HtrPayloadWithdrawalLoopMemory
import InitECandidate.Runtime.HtrPayloadWithdrawalBlockReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_withdrawal_block_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array roots count chunks heap mark watched : BitVec 64) (rank : Nat)
    (valid : HtrPayloadWithdrawalState array roots heap count state rank)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (chunksBefore : watched.toNat < chunks.toNat)
    (countBound : count.toNat ≤ 134217712)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ 33806089496)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : rank * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state htrPayloadWithdrawalBlock = (none,post)) :
    post.memory watched = state.memory watched := by
  obtain ⟨middle,normal,tail⟩ := seq_normal_parts (by exact run)
  have ranked := htrPayload_withdrawal_loop_ranked array roots heap count countBound heapFits rank state code valid (by omega)
  rw [normal] at ranked
  obtain ⟨nextRank,nextValid,nextCode,_⟩ := ranked.2.2.2 rfl
  have loopFrame := htrPayload_withdrawal_loop_normal_memory pointer accelerator zeroHashes array roots heap count watched
    countBound rootsAligned rootsFits rootsBefore heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside state middle rank code valid atPointer atAccel atZero (by omega) normal
  have rel : NormalRel HeapGlobalsRel (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep) := by
    apply normalRel_while heapGlobalsRel_preorder
    unfold htrPayloadWithdrawalStep
    apply normalRel_seq heapGlobalsRel_preorder
    · exact normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrWithdrawal_lookup
        (NormalRel.returned htrWithdrawal_normal_heapGlobals)
    · apply normalRel_heapGlobals_leaf
      intro name different
      rfl
  have globals := normalRel_apply rel (X := state) (by rw [normal]; exact Or.inl rfl) code
  rw [normal] at globals
  have keep (key : MlS) (different : key ≠ ofString "i") : middle.locals.lookup key = state.locals.lookup key :=
    htrPayload_withdrawal_loop_local_frame state middle key different normal
  have enough : htrPlistChunksCost + 1 ≤ middle.clock := by
    have spent : state.clock ≤ middle.clock + rank * (htrWithdrawalBodyCost + 2) := ranked.1
    omega
  have frame := htrPayload_withdrawal_hash_release_normal_memory middle post pointer accelerator zeroHashes chunk
    roots count chunks heap mark watched nextValid.rootsLocal nextValid.countLocal
    ((keep _ (by decide)).trans chunksLocal) ((keep _ (by decide)).trans markLocal)
    ((globals _ (by decide)).trans atPointer) ((globals _ (by decide)).trans atAccel)
    ((globals _ (by decide)).trans atChunk) ((globals _ (by decide)).trans atZero) nextValid.heapGlobal
    chunksAligned chunksFits chunksBefore countBound chunkAligned chunkFits chunkOutside heapAligned heapFits heapBefore
    accelAligned accelFits pointerFits accelOutside pointerOutside (nextCode.trans code) enough tail
  exact frame.trans loopFrame

#print axioms htrPayload_withdrawal_block_normal_memory
end InitECandidate.Runtime
