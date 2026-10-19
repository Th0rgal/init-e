import InitECandidate.Runtime.HtrPayloadHeaderVectorSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem payload_header_copy_3_bound : PayloadHeaderSuffixBound 3
    (fun count withdrawalCount => 16 + htrPayloadHeaderCost4 count withdrawalCount) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state chunksLocal chunksAligned chunksFits
    payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawLocal outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget
  change 16 + htrPayloadHeaderCost4 count withdrawalCount ≤ state.clock at budget
  let arguments : List (ExpHOL 64) := [.var .local (ofString "ch"),.op .add [.var .local (ofString "raw"),.const 0],.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word chunks),.val (.word raw),.val (.word (32#64))] := by
    simp [arguments,evalListHOLExact,evalHOLExact,chunksLocal,rawLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have first : RunBounded state (.call (some (none,none)) (ofString "memcpy") arguments) 16 :=
    evaluate_memcpy_call_bounded state arguments chunks raw (32#64)
      args code (by decide) (by change 16 ≤ state.clock; omega)
  have source : htrPayloadAt 3 = .seq (.call (some (none,none)) (ofString "memcpy") arguments) (htrPayloadAt 4) := by rfl
  rw [source]
  exact RunBounded.seq first budget (by
    intro post normal postCode remaining
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) = (none,post) at normal
    have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :=
      memcpy_call_normal_decoded_frame state post arguments chunks raw (32#64)
        payload field p n array input inputLength count.toNat args entry inside slices chunksAligned (by change _ + 32 ≤ _; omega)
        (by omega) (by omega) (by decide) code (by change 16 ≤ state.clock; omega) normal
    have keep (key : MlS) : post.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") arguments) rfl state
        (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using kept
    have globals := memcpy_call_globals_frame arguments state code
    rw [normal] at globals
    have txFrame := transfer (2#64) array count transactions (by decide)
    exact payload_header_vector_4_bound pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
      requests requestLength raw out blobs blobLength small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
      accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload post
      ((keep _).trans chunksLocal) chunksAligned chunksFits payloadChunks (postCode.trans code)
      (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
      (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal) txFrame.1 txFrame.2
      ((keep _).trans rawLocal) ((keep _).trans outLocal) ((keep _).trans payloadLocal)
      (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)).1 withdrawalBound
      (transfer (4#64) requests requestLength requestEntry (by decide)).1 requestBound
      (transfer (1#64) blobs blobLength blobEntry (by decide)).1 blobBound remaining)

#print axioms payload_header_copy_3_bound
end InitECandidate.Runtime
