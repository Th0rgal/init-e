import InitECandidate.Runtime.HtrPayloadHeaderMarkMemory
import InitECandidate.Runtime.HtrPayloadHeaderAllocationMemoryGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadHeaderAllocationMemory
import InitECandidate.Runtime.HtrPayloadHeaderMarkBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Watched memory preservation from the actual outer payload heap marker. -/
def PayloadHeaderMarkMemory_guarded (cost : BitVec 64 → BitVec 64 → Nat) : Prop :=
  ∀ (pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength watched : BitVec 64)
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
    (blobEntry : RlpSliceEntry state payload (1#64) blobs blobLength)
    (blobBound : blobLength.toNat ≤ 134217712)
    (budget : cost count withdrawalCount ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 1) = (some (.returned value),post)),
    post.memory watched = state.memory watched

theorem payload_header_mark_memory_guarded : PayloadHeaderMarkMemory_guarded htrPayloadHeaderMarkCost := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength watched small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state post value layout
    code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawLocal outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget run
  have source : htrPayloadAt 1 = .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrPayloadAt 2) := by rfl
  have reached := evaluate_heapMark_declaration_reaches state (ofString "mark") heap (htrPayloadAt 2)
    code heapGlobal (by unfold htrPayloadHeaderMarkCost at budget; omega)
  rw [← source] at reached
  obtain ⟨next,facts,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrPayloadAt 1) (htrPayloadAt 2)
    _ 1 value reached (by rw [run])
  obtain ⟨locals,memory,globals,installed,domain⟩ := facts
  have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have marker : next.locals.lookup (ofString "mark") = some (.val (.word heap)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have entry (field p n : BitVec 64) (old : RlpSliceEntry state payload field p n) : RlpSliceEntry next payload field p n :=
    old.after_frame state next payload field p n domain (congrFun memory _) (congrFun memory _)
  have nextSlices := slices.after_interval_frame state next array input inputLength count.toNat (by omega) domain
    (fun w _ _ => congrFun memory w)
  have remaining : htrPayloadHeaderAllocationCost count withdrawalCount ≤ next.clock := by
    change 1 + htrPayloadHeaderAllocationCost count withdrawalCount ≤ state.clock at budget
    generalize htrPayloadHeaderAllocationCost count withdrawalCount = cost at budget ⊢
    omega
  have suffix := payload_header_allocation_memory_guarded pointer accelerator zeroHashes chunk array heap input inputLength count payload
    withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength heap watched small countBound arrayHeap chunkAligned chunkFits
    heapAligned heapFits accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload next
    (evaluateHOLFiniteState next (htrPayloadAt 2)).2 value (layout.transfer globals installed) marker (installed.trans code)
    (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
    (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal) (entry _ _ _ transactions) nextSlices
    ((keep _ (by decide)).trans rawLocal) ((keep _ (by decide)).trans outLocal) ((keep _ (by decide)).trans payloadLocal)
    (entry _ _ _ withdrawals) withdrawalBound (entry _ _ _ requestEntry) requestBound (entry _ _ _ blobEntry) blobBound remaining
    (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (htrPayloadAt 2)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,suffix]
  exact congrFun memory watched

#print axioms payload_header_mark_memory_guarded
end InitECandidate.Runtime
