import InitECandidate.Runtime.HtrPayloadTxMarkMemory
import InitECandidate.Runtime.HtrPayloadTxMetadataSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual transaction metadata declarations preserve the watched word
through the complete transaction, withdrawal and final hashing suffix. -/
theorem htrPayload_tx_metadata_suffix_returned_memory (pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount requests requestLength raw out outerMark watched : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state pointer accelerator zeroHashes chunk heap out watched)
    (outerLocal : state.locals.lookup (ofString "mark") = some (.val (.word outerMark)))
    (watchedChunks : watched.toNat < chunks.toNat)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat)
    (code : state.code = originalRuntimeCode)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (transactions : RlpSliceEntry state payload (2#64) array count)
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (withdrawals : RlpSliceEntry state payload (3#64) withdrawalArray withdrawalCount)
    (withdrawalBound : withdrawalCount.toNat ≤ 134217712)
    (requestEntry : RlpSliceEntry state payload (4#64) requests requestLength)
    (requestBound : requestLength.toNat ≤ 134217712)
    (budget : 1 + (2 + ((count.toNat * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount)) ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 16) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reached := htrPayload_tx_metadata_reaches state payload array count payloadLocal transactions
  obtain ⟨next,equal,_,_,agreement,normal⟩ := reaches_returned_continuation state (htrPayloadAt 16) (htrPayloadAt 18)
    _ 0 value reached (by rw [run])
  subst next
  let ready := setVarHOLFinite (ofString "ntx") (.val (.word count))
    (setVarHOLFinite (ofString "txs") (.val (.word array)) state)
  have keep (key : MlS) (notArray : key ≠ ofString "txs") (notCount : key ≠ ofString "ntx") :
      ready.locals.lookup key = state.locals.lookup key := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notArray,Ne.symm notCount]
  have arrayLocal : ready.locals.lookup (ofString "txs") = some (.val (.word array)) := by
    simp (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have countLocal : ready.locals.lookup (ofString "ntx") = some (.val (.word count)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have nextSlices : RlpSliceInputPrefix ready array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,old⟩ := slices slot inside
    exact ⟨p,n,old.after_frame state ready array slot p n input inputLength rfl rfl rfl⟩
  have nextWithdrawals := withdrawals.after_frame state ready payload (3#64) withdrawalArray withdrawalCount rfl rfl rfl
  have nextRequests := requestEntry.after_frame state ready payload (4#64) requests requestLength rfl rfl rfl
  have suffix := htrPayload_tx_mark_suffix_returned_memory pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks
    withdrawalArray withdrawalCount requests requestLength raw out outerMark watched small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload ready
    (evaluateHOLFiniteState ready (htrPayloadAt 18)).2 value (layout.transfer rfl rfl)
    ((keep _ (by decide) (by decide)).trans outerLocal) watchedChunks
    ((keep _ (by decide) (by decide)).trans chunksLocal) chunksAligned chunksFits payloadChunks code
    pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal arrayLocal countLocal nextSlices
    ((keep _ (by decide) (by decide)).trans rawLocal) ((keep _ (by decide) (by decide)).trans outLocal)
    ((keep _ (by decide) (by decide)).trans payloadLocal) nextWithdrawals withdrawalBound nextRequests requestBound budget (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState ready (htrPayloadAt 18)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,suffix]
  rfl

#print axioms htrPayload_tx_metadata_suffix_returned_memory
end InitECandidate.Runtime
