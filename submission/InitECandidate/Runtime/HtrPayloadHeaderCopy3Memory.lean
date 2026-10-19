import InitECandidate.Runtime.HtrPayloadHeaderVectorMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The original first header copy uses the chunks variable directly. Its
actual argument shape retains metadata and watched memory through final return. -/
theorem payload_header_copy_3_memory : PayloadHeaderSuffixMemory 3
    (fun count wd => 16 + htrPayloadHeaderCost4 count wd) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state post value layout outerLocal watchedChunks
    chunksLocal chunksAligned chunksFits payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices
    rawLocal outLocal payloadLocal withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget run
  change 16 + htrPayloadHeaderCost4 count withdrawalCount ≤ state.clock at budget
  let arguments : List (ExpHOL 64) := [.var .local (ofString "ch"),.op .add [.var .local (ofString "raw"),.const 0],.const 32]
  have source : htrPayloadAt 3 = .seq (.call (some (none,none)) (ofString "memcpy") arguments) (htrPayloadAt 4) := by rfl
  rw [source] at run
  obtain ⟨middle,normal,rest⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ rfl state v) run
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word chunks),.val (.word raw),.val (.word (32#64))] := by
    simp [arguments,evalListHOLExact,evalHOLExact,chunksLocal,rawLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have aligned : chunks.toNat % 8 = 0 := chunksAligned
  have separation := memcpy_interval_separate chunks (32#64) watched aligned
    (by change _ + 32 ≤ _; omega) (Or.inl (by omega))
  have frame := memcpy_call_normal_memory state middle arguments chunks raw (32#64) watched
    args code (fun offset inside => (separation offset inside).1) (fun offset inside => (separation offset inside).2)
    (by decide) (by change 16 ≤ state.clock; omega) normal
  have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :=
    memcpy_call_normal_decoded_frame state middle arguments chunks raw (32#64)
      payload field p n array input inputLength count.toNat args entry inside slices aligned (by change _ + 32 ≤ _; omega)
      (by omega) (by omega) (by decide) code (by change 16 ≤ state.clock; omega) normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") arguments) rfl state
      (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have globals := memcpy_call_globals_frame arguments state code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") arguments)
  have bounded := evaluate_memcpy_call_bounded state arguments chunks raw (32#64)
    args code (by decide) (by change 16 ≤ state.clock; omega)
  unfold RunBounded at bounded
  rw [normal] at globals metadata bounded
  have spent : state.clock ≤ middle.clock + 16 := bounded.1
  have txFrame := transfer (2#64) array count transactions (by decide)
  have suffix := payload_header_vector_4_memory pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload middle post value (layout.transfer globals metadata.1)
    ((keep _).trans outerLocal) watchedChunks ((keep _).trans chunksLocal) chunksAligned chunksFits payloadChunks (metadata.1.trans code)
    (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
    (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal) txFrame.1 txFrame.2
    ((keep _).trans rawLocal) ((keep _).trans outLocal) ((keep _).trans payloadLocal)
    (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)).1 withdrawalBound
    (transfer (4#64) requests requestLength requestEntry (by decide)).1 requestBound
    (transfer (1#64) blobs blobLength blobEntry (by decide)).1 blobBound (by omega) rest
  exact suffix.trans frame

#print axioms payload_header_copy_3_memory
end InitECandidate.Runtime
