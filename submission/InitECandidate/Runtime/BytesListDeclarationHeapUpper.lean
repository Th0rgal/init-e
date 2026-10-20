import InitECandidate.Runtime.SszSplitReturnedHeapUpper
import InitECandidate.Runtime.StatelessHeapGrowth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem ret_bytesListDecl_heap_upper {F : Type} (t post : PanSemStateFiniteExact 64 F) (name : MlS) (args : List (ExpHOL 64))
    (rest : ProgHOL 64) (P L LIM MAXB Hc : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hargs : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address)) args =
      some [.val (.word P), .val (.word L), .val (.word LIM), .val (.word MAXB)])
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc)))
    (hb : Hc.toNat ≤ 33806089496) (ha : Hc.toNat % 8 = 0)
    (run : evaluateHOLFiniteState t (.decCall name (.comb [.one,.one]) (ofString "decode_bytes_list") args rest) =
      (some (.returned v), post)) :
    ∃ (t' output : PanSemStateFiniteExact 64 F) (arr cnt : BitVec 64),
      (∀ k, k ≠ name → t'.locals.lookup k = t.locals.lookup k) ∧
      t'.locals.lookup name = some (.rStruct [.val (.word arr), .val (.word cnt)]) ∧ t'.code = t.code ∧
      HeapGrowUpper Hc L t t' ∧
      evaluateHOLFiniteState t' rest = (some (.returned v), output) ∧ post.globals = output.globals ∧
      post.memory = output.memory := by
  have lookup := pan_four_word_shape_lookup t.code.lookup (ofString "decode_bytes_list") (ofString "p") (ofString "len")
    (ofString "lim") (ofString "maxb") (sourceFunctionBody Guest.guestFn_decode_bytes_list) (.comb [.one,.one])
    P L LIM MAXB (by decide_cbv) (by decide_cbv) (by decide_cbv) (by decide_cbv) (by decide_cbv) (by decide_cbv)
    (by rw [code]; exact originalRuntimeCode_decodeBytesList_lookup)
  obtain ⟨value, bodyPost, output, bodyRun, _, tail, postEq⟩ := evaluate_decCall_checked_returned_exact_scope t post
    name (ofString "decode_bytes_list") (.comb [.one,.one]) (.comb [.one,.one]) args _ _ rest _ v hargs lookup run
  generalize hentry : callEntryStateHOLFinite t ((((HolFiniteMapExact.empty.update (ofString "p", .val (.word P))).update
    (ofString "len", .val (.word L))).update (ofString "lim", .val (.word LIM))).update
    (ofString "maxb", .val (.word MAXB))) = entry at bodyRun
  have n1 : ofString "len" ≠ ofString "p" := by decide_cbv
  have n2 : ofString "lim" ≠ ofString "p" := by decide_cbv
  have n3 : ofString "maxb" ≠ ofString "p" := by decide_cbv
  have n4 : ofString "lim" ≠ ofString "len" := by decide_cbv
  have n5 : ofString "maxb" ≠ ofString "len" := by decide_cbv
  have n6 : ofString "maxb" ≠ ofString "lim" := by decide_cbv
  have body := evaluate_decodeBytesList_body entry P L LIM MAXB Hc (by rw [← hentry]; exact code)
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n1, n2, n3])
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n4, n5])
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n6])
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (by rw [← hentry]; exact heap) hb
  rw [bodyRun] at body
  obtain ⟨clock, splitPost, _, ret, _, _, og, _, _⟩ := body.2.2.2.2 value rfl
  obtain ⟨arr, cnt, hv, _, _⟩ := sszSplitReturned_count _ _ _ _ _ value ret
  obtain ⟨H', h1, h2, h3, h4, hupper, h5⟩ := sszSplitReturned_heap_upper _ splitPost L LIM Hc value
    (by rw [← hentry]; exact heap) hb ha ret
  have mt := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_bytes_list)
  rw [bodyRun] at mt
  subst hv
  refine ⟨setVarHOLFinite name (.rStruct [.val (.word arr), .val (.word cnt)]) {bodyPost with locals := t.locals},
    output, arr, cnt, fun k hk => ?_, ?_, ?_, ⟨H', ?_, h2, h3, h4, hupper, fun k hk => ?_⟩, tail, by rw [postEq],
    by rw [postEq]⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.code = t.code; rw [mt.1, ← hentry]; rfl
  · show bodyPost.globals.lookup _ = _; rw [og]; exact h1
  · show bodyPost.globals.lookup k = t.globals.lookup k; rw [og, h5 k hk, ← hentry]; rfl

#print axioms ret_bytesListDecl_heap_upper

end InitECandidate.Runtime
