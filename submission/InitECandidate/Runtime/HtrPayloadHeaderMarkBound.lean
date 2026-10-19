import InitECandidate.Runtime.HtrPayloadHeaderAllocationBound
import InitECandidate.Runtime.HeapMarkDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option linter.unusedVariables false in
/-- Entry to the actual heap marker, before the header allocation. -/
def PayloadHeaderMarkBound (cost : BitVec 64 → BitVec 64 → Nat) : Prop :=
  ∀ (pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (budget : cost count withdrawalCount ≤ state.clock),
    RunBounded state (htrPayloadAt 1) (cost count withdrawalCount)

def htrPayloadHeaderMarkCost (count withdrawalCount : BitVec 64) : Nat :=
  1 + htrPayloadHeaderAllocationCost count withdrawalCount

theorem payload_header_mark_bound : PayloadHeaderMarkBound htrPayloadHeaderMarkCost := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state
    code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawLocal outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget
  change 1 + htrPayloadHeaderAllocationCost count withdrawalCount ≤ state.clock at budget
  have source : htrPayloadAt 1 = .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrPayloadAt 2) := by rfl
  have reached := evaluate_heapMark_declaration_reaches state (ofString "mark") heap (htrPayloadAt 2) code heapGlobal (by omega)
  rw [← source] at reached
  exact evaluate_reaches_terminal_bounded state (htrPayloadAt 1) (htrPayloadAt 2) _ 1 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,memory,globals,installed,domain⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have entry (field p n : BitVec 64) (old : RlpSliceEntry state payload field p n) : RlpSliceEntry next payload field p n :=
      old.after_frame state next payload field p n domain (congrFun memory _) (congrFun memory _)
    have nextSlices := slices.after_interval_frame state next array input inputLength count.toNat (by omega) domain
      (fun watched _ _ => congrFun memory watched)
    exact payload_header_allocation_bound pointer accelerator zeroHashes chunk array heap input inputLength count payload
      withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength small countBound arrayHeap chunkAligned chunkFits
      heapAligned heapFits accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload next (installed.trans code)
      (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
      (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal) (entry _ _ _ transactions) nextSlices
      ((keep _ (by decide)).trans rawLocal) ((keep _ (by decide)).trans outLocal) ((keep _ (by decide)).trans payloadLocal)
      (entry _ _ _ withdrawals) withdrawalBound (entry _ _ _ requestEntry) requestBound (entry _ _ _ blobEntry) blobBound remaining)

#print axioms payload_header_mark_bound
end InitECandidate.Runtime
