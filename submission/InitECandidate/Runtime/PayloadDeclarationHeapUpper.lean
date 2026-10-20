import InitECandidate.Runtime.PayloadReturnedHeapUpper
import InitECandidate.Runtime.StatelessPayloadSuffixReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000000
theorem ret_payloadDecl_heap_upper {F : Type} (t post : PanSemStateFiniteExact 64 F) (name : MlS) (args : List (ExpHOL 64))
    (rest : ProgHOL 64) (A B offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hargs : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address)) args =
      some [.val (.word A), .val (.word B)])
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (heapArena : ∀ a : BitVec 64, a.toNat % 8 = 0 → H.toNat ≤ a.toNat → a.toNat < 33806089496 → t.memaddrs a)
    (scratchDom : t.memaddrs (offsets + 0) ∧ t.memaddrs (offsets + 8) ∧ t.memaddrs (offsets + 16) ∧
      t.memaddrs (offsets + 24))
    (scratchBelow : offsets.toNat + 32 ≤ H.toNat) (inputFits : A.toNat + B.toNat < 2 ^ 64)
    (run : evaluateHOLFiniteState t (.decCall name .one (ofString "decode_payload") args rest) =
      (some (.returned v), post)) :
    ∃ (t1 output : PanSemStateFiniteExact 64 F) (nextHeap array count : BitVec 64),
      t1.memory (H + 32) = .word array ∧ t1.memory (H + 40) = .word count ∧
      count.toNat ≤ B.toNat / 4 ∧ array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧
      RlpSliceInputPrefix t1 array A B count.toNat ∧ (count = 0 ∨ H.toNat + 136 ≤ array.toNat) ∧
      (∀ k, k ≠ name → t1.locals.lookup k = t.locals.lookup k) ∧
      t1.locals.lookup name = some (.val (.word H)) ∧ t1.code = t.code ∧ t1.memaddrs = t.memaddrs ∧
      540 ≤ B.toNat ∧ t1.memory (H + 0) = .word A ∧ t1.memory (H + 8) = .word B ∧
      t1.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧ H.toNat + 136 ≤ nextHeap.toNat ∧
      (∀ k, k ≠ ofString "heap_ptr" → t1.globals.lookup k = t.globals.lookup k) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → w ≠ offsets → w ≠ offsets + 8 → w ≠ offsets + 16 → w ≠ offsets + 24 →
        t1.memory w = t.memory w) ∧
      evaluateHOLFiniteState t1 rest = (some (.returned v), output) ∧ post.globals = output.globals ∧
      post.memory = output.memory ∧ post.memaddrs = output.memaddrs ∧nextHeap.toNat≤H.toNat+4*B.toNat+143 := by
  have pl : ofString "p" ≠ ofString "len" := by decide_cbv
  have lookup := pan_two_word_lookup_shape t.code.lookup (ofString "decode_payload") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_payload) .one A B pl
    (by rw [code]; exact originalRuntimeCode_decodePayload_lookup)
  obtain ⟨value, bodyPost, output, bodyRun, _, tail, postEq⟩ := evaluate_decCall_checked_returned_exact_scope t post
    name (ofString "decode_payload") .one .one args _ _ rest _ v hargs lookup run
  generalize hentry : callEntryStateHOLFinite t ((HolFiniteMapExact.empty.update (ofString "p", .val (.word A))).update
    (ofString "len", .val (.word B))) = e at bodyRun
  have ep : e.locals.lookup (ofString "p") = some (.val (.word A)) := by
    rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm pl]
  have el : e.locals.lookup (ofString "len") = some (.val (.word B)) := by
    rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have eg : e.globals = t.globals := by rw [← hentry]; rfl
  have ed : e.memaddrs = t.memaddrs := by rw [← hentry]; rfl
  have em : e.memory = t.memory := by rw [← hentry]; rfl
  have ec : e.code = originalRuntimeCode := by rw [← hentry]; exact code
  have cap := (payload_body_returned_allocation_capacity e bodyPost B H value el ec (by rw [eg]; exact heap) hb bodyRun).2
  have hd : ∀ c : BitVec 64, c.toNat ≤ 40 → c.toNat % 8 = 0 → e.memaddrs (H + c) := by
    intro c hc cellAligned; rw [ed]; apply heapArena <;> rw [BitVec.toNat_add] <;> omega
  have hv := payload_body_returned_value e bodyPost A B offsets H value ep el (by rw [eg]; exact hg)
    (by rw [eg]; exact heap) hb ha inputFits (by rw [ed]; exact scratchDom.1) (by rw [ed]; exact scratchDom.2.1)
    (by rw [ed]; exact scratchDom.2.2.1) (by rw [ed]; exact scratchDom.2.2.2) (hd 0 (by decide) (by decide)) (hd 8 (by decide) (by decide))
    (hd 16 (by decide) (by decide)) (hd 24 (by decide) (by decide)) (hd 32 (by decide) (by decide)) (hd 40 (by decide) (by decide)) ec bodyRun
  subst hv
  obtain ⟨long, array, count, nextHeap, slices, countBound, read32, read40, nextGlobal, nextBound, nextAligned, growth, arrayBefore, above, upper⟩ :=
    payload_body_returned_slices_heap_upper e bodyPost A B offsets H _ ep el (by rw [eg]; exact hg)
      (by rw [eg]; exact heap) hb ha inputFits (by rw [ed]; exact scratchDom.1) (by rw [ed]; exact scratchDom.2.1)
      (by rw [ed]; exact scratchDom.2.2.1) (by rw [ed]; exact scratchDom.2.2.2) (hd 0 (by decide) (by decide)) (hd 8 (by decide) (by decide))
      (hd 16 (by decide) (by decide)) (hd 24 (by decide) (by decide)) (hd 32 (by decide) (by decide)) (hd 40 (by decide) (by decide)) ec bodyRun
  obtain ⟨h0, h8, gframe⟩ := payload_body_returned_header e bodyPost A B offsets H _ ep el (by rw [eg]; exact hg)
      (by rw [eg]; exact heap) hb ha scratchBelow (by rw [ed]; exact scratchDom.1) (by rw [ed]; exact scratchDom.2.1)
      (by rw [ed]; exact scratchDom.2.2.1) (by rw [ed]; exact scratchDom.2.2.2) (hd 0 (by decide) (by decide)) (hd 8 (by decide) (by decide))
      (hd 16 (by decide) (by decide)) (hd 24 (by decide) (by decide)) (hd 32 (by decide) (by decide)) (hd 40 (by decide) (by decide)) ec bodyRun
  have mt := evaluateHOLFiniteState_metadata e (sourceFunctionBody Guest.guestFn_decode_payload)
  rw [bodyRun] at mt
  refine ⟨setVarHOLFinite name (.val (.word H)) {bodyPost with locals := t.locals}, output, nextHeap, array, count,
    read32, read40, countBound, arrayBefore, ?_, above,
    fun k hk => ?_, ?_, ?_, ?_, long, h0, h8, nextGlobal, nextBound, nextAligned, growth, fun k hk => ?_,
    fun w below s0 s8 s16 s24 => ?_, tail, by rw [postEq], by rw [postEq], by rw [postEq],upper⟩
  · intro index inside
    obtain ⟨p, n, item⟩ := slices index inside
    exact ⟨p, n, item.after_frame bodyPost _ array index p n A B rfl rfl rfl⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.code = t.code; rw [mt.1, ec, code]
  · show bodyPost.memaddrs = t.memaddrs; rw [mt.2.1, ed]
  · show bodyPost.globals.lookup k = t.globals.lookup k; rw [gframe k hk, eg]
  · show bodyPost.memory w = t.memory w
    rw [payload_body_returned_below e bodyPost A B offsets H w _ ep el (by rw [eg]; exact hg)
      (by rw [eg]; exact heap) hb ha (by rw [ed]; exact scratchDom.1) (by rw [ed]; exact scratchDom.2.1)
      (by rw [ed]; exact scratchDom.2.2.1) (by rw [ed]; exact scratchDom.2.2.2) (hd 0 (by decide) (by decide)) (hd 8 (by decide) (by decide))
      (hd 16 (by decide) (by decide)) (hd 24 (by decide) (by decide)) (hd 32 (by decide) (by decide)) (hd 40 (by decide) (by decide)) below ⟨s0, s8, s16, s24⟩ ec
      bodyRun, em]

#print axioms ret_payloadDecl_heap_upper
end InitECandidate.Runtime
