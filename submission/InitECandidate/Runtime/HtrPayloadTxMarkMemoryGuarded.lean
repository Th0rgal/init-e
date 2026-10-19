import InitECandidate.Runtime.HtrPayloadTxMarkMemory
import InitECandidate.Runtime.HtrPayloadTxAllocationMemoryGuarded
import InitECandidate.Runtime.HtrPayloadTxAllocationMemory
import InitECandidate.Runtime.HtrPayloadTxMarkSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual saved inner heap marker supplies the frontier used by both
transaction and withdrawal releases while preserving decoded and watched memory. -/
theorem htrPayload_tx_mark_suffix_returned_memory_guarded (pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount requests requestLength raw out outerMark watched : BitVec 64)
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
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count)))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (withdrawals : RlpSliceEntry state payload (3#64) withdrawalArray withdrawalCount)
    (withdrawalBound : withdrawalCount.toNat ≤ 134217712)
    (requestEntry : RlpSliceEntry state payload (4#64) requests requestLength)
    (requestBound : requestLength.toNat ≤ 134217712)
    (budget : 1 + (2 + ((count.toNat * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount)) ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 18) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reached := evaluate_heapMark_declaration_reaches state (ofString "m2") heap (htrPayloadAt 19)
    code heapGlobal (by omega)
  rw [← source_htrPayload_tx_mark] at reached
  obtain ⟨next,facts,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrPayloadAt 18) (htrPayloadAt 19)
    _ 1 value reached (by rw [run])
  obtain ⟨locals,memory,globals,installed,domain⟩ := facts
  have keep (key : MlS) (different : key ≠ ofString "m2") : next.locals.lookup key = state.locals.lookup key := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have marker : next.locals.lookup (ofString "m2") = some (.val (.word heap)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have nextSlices : RlpSliceInputPrefix next array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,old⟩ := slices slot inside
    exact ⟨p,n,old.after_frame state next array slot p n input inputLength domain (congrFun memory _) (congrFun memory _)⟩
  have nextWithdrawals := withdrawals.after_frame state next payload (3#64) withdrawalArray withdrawalCount domain
    (congrFun memory _) (congrFun memory _)
  have nextRequests := requestEntry.after_frame state next payload (4#64) requests requestLength domain
    (congrFun memory _) (congrFun memory _)
  let tailCost := 2 + ((count.toNat * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount)
  have remaining : tailCost ≤ next.clock := by
    change 1 + tailCost ≤ state.clock at budget
    generalize tailCost = cost at budget ⊢
    omega
  have suffix := htrPayload_tx_allocation_suffix_returned_memory_guarded pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks heap
    withdrawalArray withdrawalCount requests requestLength raw out outerMark watched small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload next
    (evaluateHOLFiniteState next (htrPayloadAt 19)).2 value (layout.transfer globals installed)
    ((keep _ (by decide)).trans outerLocal) watchedChunks layout.heapBefore
    ((keep _ (by decide)).trans chunksLocal) marker chunksAligned chunksFits payloadChunks (installed.trans code)
    (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
    (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal)
    ((keep _ (by decide)).trans arrayLocal) ((keep _ (by decide)).trans countLocal) nextSlices
    ((keep _ (by decide)).trans rawLocal) ((keep _ (by decide)).trans outLocal) ((keep _ (by decide)).trans payloadLocal)
    heapAligned heapFits payloadHeap nextWithdrawals withdrawalBound nextRequests requestBound remaining (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (htrPayloadAt 19)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,suffix]
  exact congrFun memory watched

#print axioms htrPayload_tx_mark_suffix_returned_memory_guarded
end InitECandidate.Runtime
