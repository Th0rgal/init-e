import InitECandidate.Runtime.HtrPayloadBytesListSuffixBound
import InitECandidate.Runtime.HtrPayloadHeaderCopy14Guarded
import InitECandidate.Runtime.HtrPayloadBytesListSource
import InitECandidate.Runtime.HtrPayloadHeaderCopy14Bound
import InitECandidate.Runtime.HtrBytesListGlobals
import InitECandidate.Runtime.HtrBytesListMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_htrPayload_bytes_list_suffix_guarded (pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (arrayChunks : array.toNat + count.toNat * 16 ≤ chunks.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (pointerFits : count ≠ 0 → pointer.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (blobEntry : RlpSliceEntry state payload (1#64) blobs blobLength)
    (blobBound : blobLength.toNat ≤ 134217712)
    (budget : (htrBytesListBodyCost + 1) + (16 + (16 + htrPayloadTxMetadataCost count withdrawalCount)) ≤ state.clock) :
    RunBounded state (htrPayloadAt 13) ((htrBytesListBodyCost + 1) + (16 + (16 + htrPayloadTxMetadataCost count withdrawalCount))) := by
  let arguments := htrPayloadBytesListArguments
  have args := htrPayload_bytes_list_arguments state payload blobs blobLength chunks payloadLocal chunksLocal blobEntry
  have first := runBounded_htrBytesList_call state none arguments blobs blobLength (1#64) (chunks + (320#64)) heap
    args blobBound heapGlobal heapFits code (by omega)
  have natural : (chunks + (320#64)).toNat = chunks.toNat + 320 := by
    apply BitVec.toNat_add_of_lt
    change chunks.toNat + 320 < 2 ^ 64
    omega
  have aligned : (chunks + (320#64)).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,chunksAligned]
  rw [source_htrPayload_bytes_list]
  exact RunBounded.seq first budget (by
    intro next normal nextCode remaining
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_list") arguments) = (none,next) at normal
    have frame (watched : BitVec 64) (lower : payload.toNat ≤ watched.toNat ∨ (count ≠ 0 ∧ array.toNat ≤ watched.toNat))
        (beforeChunks : watched.toNat < chunks.toNat) (beforeHeap : watched.toNat < heap.toNat) :
        next.memory watched = state.memory watched := by
      have bounds : chunk.toNat + 32 ≤ watched.toNat ∧ accelerator.toNat + 96 ≤ watched.toNat ∧ pointer.toNat + 64 ≤ watched.toNat := by
        rcases lower with lo | ⟨nz,lo⟩
        · exact ⟨by omega,by omega,by omega⟩
        · have := chunkFits nz
          have := accelFits nz
          have := pointerFits nz
          exact ⟨by omega,by omega,by omega⟩
      exact htrBytesList_call_normal_memory state next arguments pointer accelerator zeroHashes chunk blobs blobLength (1#64) heap
        (chunks + (320#64)) watched args pointerGlobal accelGlobal chunkGlobal chunkAligned (by omega)
        (Or.inr bounds.1) zeroGlobal heapGlobal aligned (by rw [natural]; omega)
        (Or.inl (by rw [natural]; omega)) blobBound heapAligned heapFits beforeHeap accelAligned (by omega) (by omega)
        (Or.inr bounds.2.1) (Or.inr bounds.2.2) code (by omega) normal
    have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_bytes_list") arguments)
    rw [normal] at metadata
    have transfer (index p n : BitVec 64) (entry : RlpSliceEntry state payload index p n) (inside : index.toNat ≤ 4) :
        RlpSliceEntry next payload index p n := by
      apply entry.after_record_frame state next payload index p n inside (by omega) metadata.2.1
      intro watched lo hi
      exact frame watched (Or.inl lo) (by omega) (by omega)
    have nextSlices : RlpSliceInputPrefix next array input inputLength count.toNat := by
      apply slices.after_interval_frame state next array input inputLength count.toNat (by have := chunks.isLt; omega) metadata.2.1
      intro watched lo hi
      exact frame watched (Or.inr ⟨(by intro zero; subst count; simp at hi; omega),lo⟩) (Nat.lt_of_lt_of_le hi arrayChunks) (Nat.lt_of_lt_of_le hi arrayHeap)
    have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_bytes_list") arguments) rfl state
        (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using kept
    have globals := htrBytesList_call_normal_globals state next arguments blobs blobLength (1#64) (chunks + (320#64)) heap
      args heapGlobal code normal
    exact runBounded_htrPayload_header_copy14_suffix_guarded pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks
      withdrawalArray withdrawalCount requests requestLength raw out small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
      accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload next
      ((keep _).trans chunksLocal) chunksAligned chunksFits payloadChunks (nextCode.trans code)
      (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
      (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal)
      (transfer (2#64) array count transactions (by decide)) nextSlices
      ((keep _).trans rawLocal) ((keep _).trans outLocal) ((keep _).trans payloadLocal)
      (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)) withdrawalBound
      (transfer (4#64) requests requestLength requestEntry (by decide)) requestBound remaining)

#print axioms runBounded_htrPayload_bytes_list_suffix_guarded
end InitECandidate.Runtime
