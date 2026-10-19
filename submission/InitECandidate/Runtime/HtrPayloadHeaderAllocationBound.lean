import InitECandidate.Runtime.HtrPayloadHeaderCopy3Bound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option linter.unusedVariables false in
/-- Entry to the actual 608-byte header allocation, before a chunks pointer exists. -/
def PayloadHeaderAllocationBound (cost : BitVec 64 → BitVec 64 → Nat) : Prop :=
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
    RunBounded state (htrPayloadAt 2) (cost count withdrawalCount)

def htrPayloadHeaderAllocationCost (count withdrawalCount : BitVec 64) : Nat :=
  2 + (16 + htrPayloadHeaderCost4 count withdrawalCount)

theorem payload_header_allocation_bound : PayloadHeaderAllocationBound htrPayloadHeaderAllocationCost := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state
    code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawLocal outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget
  change 2 + (16 + htrPayloadHeaderCost4 count withdrawalCount) ≤ state.clock at budget
  let argument : ExpHOL 64 := .panop .mul [.const 19,.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word (608#64))] := by
    simp [argument,evalListHOLExact,evalHOLExact,wordOpHOL,wordOp,panOpHOL,isWfShapeExactHOL,valueIsWord,valueWord]
  have source : htrPayloadAt 2 = .decCall (ofString "ch") .one (ofString "alloc") [argument] (htrPayloadAt 3) := by rfl
  have reached := evaluate_allocation_declaration_reaches state argument (ofString "ch") heap (608#64) (htrPayloadAt 3)
    args code heapGlobal heapFits (by omega)
  rw [← source] at reached
  exact evaluate_reaches_terminal_bounded state (htrPayloadAt 2) (htrPayloadAt 3) _ 2 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,memory,installed,domain,globals,cap,covers,aligned⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "ch") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") : next.globals.lookup key = state.globals.lookup key := by
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have entry (field p n : BitVec 64) (old : RlpSliceEntry state payload field p n) : RlpSliceEntry next payload field p n :=
      old.after_frame state next payload field p n domain (congrFun memory _) (congrFun memory _)
    have nextSlices := slices.after_interval_frame state next array input inputLength count.toNat (by omega) domain (fun watched _ _ => congrFun memory watched)
    have coversNat : heap.toNat + 608 ≤ (allocationEnd heap (608#64)).toNat := by exact covers
    exact payload_header_copy_3_bound pointer accelerator zeroHashes chunk array (allocationEnd heap (608#64)) input inputLength count
      payload heap withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength small countBound (by omega) arrayHeap
      chunkAligned chunkFits aligned cap accelAligned accelFits pointerFits (by omega) chunkPayload accelPayload pointerPayload next
      (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]) heapAligned (by omega) payloadHeap (installed.trans code)
      ((nonHeap _ (by decide)).trans pointerGlobal) ((nonHeap _ (by decide)).trans accelGlobal)
      ((nonHeap _ (by decide)).trans zeroGlobal) ((nonHeap _ (by decide)).trans chunkGlobal)
      (by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (entry _ _ _ transactions) nextSlices ((keep _ (by decide)).trans rawLocal) ((keep _ (by decide)).trans outLocal)
      ((keep _ (by decide)).trans payloadLocal) (entry _ _ _ withdrawals) withdrawalBound (entry _ _ _ requestEntry) requestBound
      (entry _ _ _ blobEntry) blobBound remaining)

#print axioms payload_header_allocation_bound
end InitECandidate.Runtime
