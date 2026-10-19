import InitECandidate.Runtime.HtrPayloadHeaderMarkBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option linter.unusedVariables false in
/-- Entry to the original payload function from decoded metadata. -/
def PayloadHeaderEntryBound (cost : BitVec 64 → BitVec 64 → Nat) : Prop :=
  ∀ (pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount requests requestLength raw rawLength out blobs blobLength : BitVec 64)
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
    (rawEntry : RlpSliceEntry state payload (0#64) raw rawLength)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (withdrawals : RlpSliceEntry state payload (3#64) withdrawalArray withdrawalCount)
    (withdrawalBound : withdrawalCount.toNat ≤ 134217712)
    (requestEntry : RlpSliceEntry state payload (4#64) requests requestLength)
    (requestBound : requestLength.toNat ≤ 134217712)
    (blobEntry : RlpSliceEntry state payload (1#64) blobs blobLength)
    (blobBound : blobLength.toNat ≤ 134217712)
    (budget : cost count withdrawalCount ≤ state.clock),
    RunBounded state (htrPayloadAt 0) (cost count withdrawalCount)

theorem payload_header_entry_bound : PayloadHeaderEntryBound htrPayloadHeaderMarkCost := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount
    requests requestLength raw rawLength out blobs blobLength small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state
    code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawEntry outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget
  have source : htrPayloadAt 0 = .dec (ofString "raw") .one
      (.load .one (.op .add [.var .local (ofString "pl"),.const 0])) (htrPayloadAt 1) := by rfl
  have pointerDomain : state.memaddrs payload := by simpa using rawEntry.pointerDomain
  have pointerCell : state.memory payload = .word raw := by simpa using rawEntry.pointerCell
  have reached : Reaches state (htrPayloadAt 0)
      (fun next => next = setVarHOLFinite (ofString "raw") (.val (.word raw)) state) 0 (htrPayloadAt 1) := by
    rw [source]
    apply reaches_dec
    intro value evaluated
    have actual : value = .val (.word raw) := by
      simpa [evalHOLExact,evalListHOLExact,payloadLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
        memLoadHOLExact,pointerDomain,pointerCell] using evaluated.symm
    subst value
    exact ⟨raw,rfl,rfl⟩
  have result := evaluate_reaches_terminal_bounded state (htrPayloadAt 0) (htrPayloadAt 1) _ 0
    (htrPayloadHeaderMarkCost count withdrawalCount) (by simpa using budget) reached (by
      intro next equal remaining
      subst next
      let next := setVarHOLFinite (ofString "raw") (.val (.word raw)) state
      have entry (field p n : BitVec 64) (old : RlpSliceEntry state payload field p n) : RlpSliceEntry next payload field p n :=
        old.after_frame state next payload field p n rfl rfl rfl
      have nextSlices := slices.after_interval_frame state next array input inputLength count.toNat (by omega) rfl
        (fun _ _ _ => rfl)
      have keep (key : MlS) (different : key ≠ ofString "raw") : next.locals.lookup key = state.locals.lookup key := by
        simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      exact payload_header_mark_bound pointer accelerator zeroHashes chunk array heap input inputLength count payload
        withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength small countBound arrayHeap chunkAligned chunkFits
        heapAligned heapFits accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload next
        code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal (entry _ _ _ transactions) nextSlices
        (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) ((keep _ (by decide)).trans outLocal)
        ((keep _ (by decide)).trans payloadLocal) (entry _ _ _ withdrawals) withdrawalBound (entry _ _ _ requestEntry) requestBound
        (entry _ _ _ blobEntry) blobBound remaining)
  simpa only [RunBounded,Nat.zero_add] using result

#print axioms payload_header_entry_bound
end InitECandidate.Runtime
