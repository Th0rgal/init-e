import InitECandidate.Runtime.HtrPayloadTxAllocationMemory
import InitECandidate.Runtime.HtrPayloadTxSuffixMemoryGuarded
import InitECandidate.Runtime.HtrPayloadTxSuffixMemory
import InitECandidate.Runtime.HtrPayloadTxAllocationSuffixBound
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual transaction roots allocation and counter declaration supply
loop geometry while keeping the caller's decoded metadata and watched memory. -/
theorem htrPayload_tx_allocation_suffix_returned_memory_guarded (pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks mark withdrawalArray withdrawalCount requests requestLength raw out outerMark watched : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (pointerFits : count ≠ 0 → pointer.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state pointer accelerator zeroHashes chunk heap out watched)
    (outerLocal : state.locals.lookup (ofString "mark") = some (.val (.word outerMark)))
    (watchedChunks : watched.toNat < chunks.toNat) (watchedMark : watched.toNat < mark.toNat)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat)
    (code : state.code = originalRuntimeCode)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count)))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (markAligned : mark.toNat % 8 = 0) (markBound : mark.toNat ≤ 33806089496)
    (payloadMark : payload.toNat + 72 < mark.toNat)
    (withdrawals : RlpSliceEntry state payload (3#64) withdrawalArray withdrawalCount)
    (withdrawalBound : withdrawalCount.toNat ≤ 134217712)
    (requestEntry : RlpSliceEntry state payload (4#64) requests requestLength)
    (requestBound : requestLength.toNat ≤ 134217712)
    (budget : 2 + ((count.toNat * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount) ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 19) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reached := htrPayload_tx_allocation_frame_reaches state pointer accelerator zeroHashes chunk array heap input inputLength count
    pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal arrayLocal countLocal slices countBound heapFits code (by omega)
  obtain ⟨next,facts,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrPayloadAt 19) (htrPayloadAt 21)
    _ 2 value reached (by rw [run])
  obtain ⟨valid,installed,rootsFit,aligned,cap,memory,domain,globals,keep,covers⟩ := facts
  have nextWithdrawals := withdrawals.after_frame state next payload (3#64) withdrawalArray withdrawalCount domain
    (congrFun memory _) (congrFun memory _)
  have nextRequests := requestEntry.after_frame state next payload (4#64) requests requestLength domain
    (congrFun memory _) (congrFun memory _)
  have nextBefore : watched.toNat < (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat := by
    have := layout.heapBefore
    omega
  have nextLayout := layout.after_heap_restore globals (installed.trans layout.code.symm) aligned cap nextBefore
  let tailCost := (count.toNat * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount
  have remaining : tailCost ≤ next.clock := by
    change 2 + tailCost ≤ state.clock at budget
    generalize tailCost = cost at budget ⊢
    omega
  have suffix := htrPayload_tx_suffix_returned_memory_guarded pointer accelerator zeroHashes chunk array heap
    (allocationEnd heap (htrPayloadTxAllocationSize count)) input inputLength count payload chunks mark
    withdrawalArray withdrawalCount requests requestLength raw out outerMark watched small countBound arrayHeap (by omega)
    heapAligned rootsFit chunkAligned chunkFits aligned cap accelAligned accelFits pointerFits payloadHeap (by omega)
    chunkPayload accelPayload pointerPayload next (evaluateHOLFiniteState next (htrPayloadAt 21)).2 count.toNat value nextLayout
    ((keep _ (by decide) (by decide)).trans outerLocal) layout.heapBefore watchedChunks watchedMark
    ((keep _ (by decide) (by decide)).trans chunksLocal) ((keep _ (by decide) (by decide)).trans markLocal)
    chunksAligned chunksFits payloadChunks installed valid
    ((keep _ (by decide) (by decide)).trans rawLocal) ((keep _ (by decide) (by decide)).trans outLocal)
    ((keep _ (by decide) (by decide)).trans payloadLocal) markAligned markBound payloadMark nextWithdrawals withdrawalBound
    nextRequests requestBound remaining (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (htrPayloadAt 21)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,suffix]
  exact congrFun memory watched

#print axioms htrPayload_tx_allocation_suffix_returned_memory_guarded
end InitECandidate.Runtime
