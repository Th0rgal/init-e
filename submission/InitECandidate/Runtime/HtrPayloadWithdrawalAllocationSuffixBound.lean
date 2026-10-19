import InitECandidate.Runtime.HtrPayloadWithdrawalSuffixBound
import InitECandidate.Runtime.HtrPayloadWithdrawalAllocationFrameReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_htrPayload_withdrawal_allocation_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array heap count chunks mark payload requests length raw out oldIndex : BitVec 64)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (lengthBound : length.toNat ≤ 134217712) (markBound : mark.toNat ≤ 33806089496)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (countBound : count.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    (code : state.code = originalRuntimeCode)
    (arrayLocal : state.locals.lookup (ofString "wd") = some (.val (.word array)))
    (countLocal : state.locals.lookup (ofString "nwd") = some (.val (.word count)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word oldIndex)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (entry : RlpSliceEntry state payload (4#64) requests length)
    (budget : 2 + ((count.toNat * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost) ≤ state.clock) :
    RunBounded state (htrPayloadAt 26)
      (2 + ((count.toNat * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost)) := by
  have reached := htrPayload_withdrawal_allocation_frame_reaches state array heap count chunks oldIndex
    arrayLocal countLocal chunksLocal indexLocal heapGlobal heapFits code (by omega)
  exact evaluate_reaches_terminal_bounded state (htrPayloadAt 26) (htrPayloadAt 28) _ 2 _ budget reached (by
    intro next facts remaining
    obtain ⟨valid,chunksKept,installed,cap,memory,domain,globals,keep,covers,aligned⟩ := facts
    have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") :
        next.globals.lookup key = state.globals.lookup key := by
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have entryKept := entry.after_frame state next payload (4#64) requests length domain
      (congrFun memory _) (congrFun memory _)
    rw [htrPayload_tx_allocation_size count countBound] at covers
    exact runBounded_htrPayload_withdrawal_suffix next pointer accelerator zeroHashes chunk array heap
      (allocationEnd heap (htrPayloadTxAllocationSize count)) count chunks mark payload requests length raw out count.toNat
      ((keep _ (by decide) (by decide)).trans rawLocal) ((keep _ (by decide) (by decide)).trans outLocal)
      ((keep _ (by decide) (by decide)).trans payloadLocal) lengthBound markBound chunksKept
      ((keep _ (by decide) (by decide)).trans markLocal) chunksAligned chunksFits payloadChunks chunkAligned chunkPayload
      ((nonHeap _ (by decide)).trans chunkGlobal) countBound heapAligned (by omega) aligned cap payloadHeap (by omega)
      accelAligned accelPayload pointerPayload installed valid ((nonHeap _ (by decide)).trans pointerGlobal)
      ((nonHeap _ (by decide)).trans accelGlobal) ((nonHeap _ (by decide)).trans zeroGlobal) entryKept remaining)

#print axioms runBounded_htrPayload_withdrawal_allocation_suffix
end InitECandidate.Runtime
