import InitECandidate.Runtime.HtrPayloadBytesListSuffixMemory
import InitECandidate.Runtime.HtrPayloadHeaderCopyMemoryGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadHeaderCopyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The real bytes-list hash retains decoded entries and transaction slices
while preserving watched memory through the complete remaining payload body. -/
theorem payload_header_bytes_list_memory_guarded : PayloadHeaderSuffixMemory_guarded 13 htrPayloadHeaderCost13 := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state post value layout outerLocal watchedChunks
    chunksLocal chunksAligned chunksFits payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices
    rawLocal outLocal payloadLocal withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget run
  rw [source_htrPayload_bytes_list] at run
  obtain ⟨middle,normal,rest⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ rfl state v) run
  let arguments := htrPayloadBytesListArguments
  have args := htrPayload_bytes_list_arguments state payload blobs blobLength chunks payloadLocal chunksLocal blobEntry
  have natural : (chunks + (320#64)).toNat = chunks.toNat + 320 := word_add_toNat chunks 320 (by omega)
  have aligned : (chunks + (320#64)).toNat % 8 = 0 := by rw [natural,Nat.add_mod,chunksAligned]
  have enough : htrBytesListBodyCost + 1 ≤ state.clock :=
    (Nat.le_add_right (htrBytesListBodyCost + 1) (16 + (16 + htrPayloadTxMetadataCost count withdrawalCount))).trans budget
  have watchedFrame := htrBytesList_call_normal_memory state middle arguments pointer accelerator zeroHashes chunk blobs blobLength (1#64) heap
    (chunks + (320#64)) watched args pointerGlobal accelGlobal chunkGlobal chunkAligned layout.chunkFits layout.chunkOutside zeroGlobal heapGlobal
    aligned (by rw [natural]; omega) (Or.inl (by rw [natural]; omega)) blobBound heapAligned heapFits layout.heapBefore accelAligned
    layout.accelFits layout.shaFits layout.accelOutside layout.shaOutside code enough normal
  have frame (w : BitVec 64) (lower : payload.toNat ≤ w.toNat ∨ (count ≠ 0 ∧ array.toNat ≤ w.toNat))
      (beforeChunks : w.toNat < chunks.toNat) (beforeHeap : w.toNat < heap.toNat) : middle.memory w = state.memory w := by
    have bounds : chunk.toNat + 32 ≤ w.toNat ∧ accelerator.toNat + 96 ≤ w.toNat ∧ pointer.toNat + 64 ≤ w.toNat := by
      rcases lower with lo | ⟨nz,lo⟩
      · exact ⟨by omega,by omega,by omega⟩
      · have := chunkFits nz
        have := accelFits nz
        have := pointerFits nz
        exact ⟨by omega,by omega,by omega⟩
    exact htrBytesList_call_normal_memory state middle arguments pointer accelerator zeroHashes chunk blobs blobLength (1#64) heap
      (chunks + (320#64)) w args pointerGlobal accelGlobal chunkGlobal chunkAligned (by omega)
      (Or.inr bounds.1) zeroGlobal heapGlobal aligned (by rw [natural]; omega)
      (Or.inl (by rw [natural]; omega)) blobBound heapAligned heapFits beforeHeap accelAligned (by omega) (by omega)
      (Or.inr bounds.2.1) (Or.inr bounds.2.2) code enough normal
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_bytes_list") arguments)
  have globals := htrBytesList_call_normal_globals state middle arguments blobs blobLength (1#64) (chunks + (320#64)) heap
    args heapGlobal code normal
  have bounded := runBounded_htrBytesList_call state none arguments blobs blobLength (1#64) (chunks + (320#64)) heap
    args blobBound heapGlobal heapFits code enough
  unfold RunBounded at bounded
  rw [normal] at metadata bounded
  have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :
      RlpSliceEntry middle payload field p n := by
    apply entry.after_record_frame state middle payload field p n inside (by omega) metadata.2.1
    intro w lo hi
    exact frame w (Or.inl lo) (by omega) (by omega)
  have nextSlices : RlpSliceInputPrefix middle array input inputLength count.toNat := by
    apply slices.after_interval_frame state middle array input inputLength count.toNat (by have := chunks.isLt; omega) metadata.2.1
    intro w lo hi
    exact frame w (Or.inr ⟨(by intro zero; subst count; simp at hi; omega),lo⟩) (Nat.lt_of_lt_of_le hi arrayChunks) (Nat.lt_of_lt_of_le hi arrayHeap)
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_bytes_list") arguments) rfl state
      (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have spent : state.clock ≤ middle.clock + (htrBytesListBodyCost + 1) := bounded.1
  have remaining : 16 + (16 + htrPayloadTxMetadataCost count withdrawalCount) ≤ middle.clock := by
    change (htrBytesListBodyCost + 1) + (16 + (16 + htrPayloadTxMetadataCost count withdrawalCount)) ≤ state.clock at budget
    generalize htrBytesListBodyCost = bc at budget spent
    generalize htrPayloadTxMetadataCost count withdrawalCount = cost at budget ⊢
    omega
  have suffix := payload_header_copy_14_memory_guarded pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload middle post value (layout.transfer globals metadata.1)
    ((keep _).trans outerLocal) watchedChunks ((keep _).trans chunksLocal) chunksAligned chunksFits payloadChunks (metadata.1.trans code)
    (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
    (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal)
    (transfer (2#64) array count transactions (by decide)) nextSlices
    ((keep _).trans rawLocal) ((keep _).trans outLocal) ((keep _).trans payloadLocal)
    (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)) withdrawalBound
    (transfer (4#64) requests requestLength requestEntry (by decide)) requestBound
    (transfer (1#64) blobs blobLength blobEntry (by decide)) blobBound remaining rest
  exact suffix.trans watchedFrame

#print axioms payload_header_bytes_list_memory_guarded
end InitECandidate.Runtime
