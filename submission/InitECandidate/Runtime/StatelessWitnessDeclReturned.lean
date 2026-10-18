import InitECandidate.Runtime.DecodeBytesListReturnedAligned
import InitECandidate.Runtime.PanFourWordShapeLookup
import InitECandidate.Runtime.PanDecReturnedScope
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.StatelessWitnessCheckBound
import InitECandidate.Runtime.StatelessPrefixStages
import InitECandidate.Runtime.DecodeRequestsBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem ret_dec {F : Type} (t post : PanSemStateFiniteExact 64 F) (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64)
    (body : ProgHOL 64) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState t (.dec name sh init body) = (some (.returned v), post)) :
    ∃ value output, evaluateHOLFiniteState (setVarHOLFinite name value t) body = (some (.returned v), output) ∧
      post.globals = output.globals := by
  obtain ⟨value, output, _, r, e⟩ := evaluate_dec_returned_scope t post name sh init body v run
  exact ⟨value, output, r, by rw [e]⟩

theorem ret_storeSeq {F : Type} (t post : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) (rest : ProgHOL 64)
    (v : ValueHOL 64) (run : evaluateHOLFiniteState t (.seq (.store d e) rest) = (some (.returned v), post)) :
    ∃ M, evaluateHOLFiniteState ({t with memory := M} : PanSemStateFiniteExact 64 F) rest = (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  rcases evaluate_store_cases t d e with err | ⟨M, ok⟩
  · rw [err] at run; simp at run
  · rw [ok] at run; exact ⟨M, run⟩

theorem ret_checkCall {F : Type} (t post : PanSemStateFiniteExact 64 F) (rest : ProgHOL 64) (offsets WL : BitVec 64)
    (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hwl : t.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (run : evaluateHOLFiniteState t (.seq statelessWitnessCheckCall rest) = (some (.returned v), post)) :
    ∃ t', evaluateHOLFiniteState t' rest = (some (.returned v), post) ∧ t'.locals = t.locals ∧
      t'.globals = t.globals ∧ t'.code = t.code := by
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessWitnessCheckArguments =
      some [.val (.word offsets), .val (.word 3), .val (.word 12), .val (.word WL)] := by
    simp [statelessWitnessCheckArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hg, hwl]
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState t statelessWitnessCheckCall with
  | mk r t' =>
    rw [callRun] at run
    cases r with
    | some x =>
      have nr := evaluate_discard_call_no_return t (ofString "ssz_check_offsets") statelessWitnessCheckArguments v
      unfold statelessWitnessCheckCall at callRun
      rw [callRun] at nr
      exact absurd (Prod.mk.inj run).1 nr
    | none =>
      dsimp only at run
      obtain ⟨_, _, eg, _, el⟩ := sszCheckOffsets_call_returned t _ offsets 3 12 WL args code (by decide) t'
        (by unfold statelessWitnessCheckCall at callRun; exact callRun)
      have mt := evaluateHOLFiniteState_metadata t statelessWitnessCheckCall
      rw [callRun] at mt
      exact ⟨t', run, el, eg, mt.1⟩

/-- Heap/global facts carried along the witness suffix. -/
def HeapFrame {F : Type} (s0 t : PanSemStateFiniteExact 64 F) : Prop :=
  (∃ H : BitVec 64, t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) ∧ H.toNat ≤ 33806089496 ∧
    H.toNat % 8 = 0) ∧ ∀ k, k ≠ ofString "heap_ptr" → t.globals.lookup k = s0.globals.lookup k

theorem ret_bytesListDecl {F : Type} (s0 t post : PanSemStateFiniteExact 64 F) (name : MlS) (args : List (ExpHOL 64))
    (rest : ProgHOL 64) (P L LIM MAXB : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hargs : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address)) args =
      some [.val (.word P), .val (.word L), .val (.word LIM), .val (.word MAXB)])
    (frame : HeapFrame s0 t)
    (run : evaluateHOLFiniteState t (.decCall name (.comb [.one,.one]) (ofString "decode_bytes_list") args rest) =
      (some (.returned v), post)) :
    ∃ t' output, (∀ k, k ≠ name → t'.locals.lookup k = t.locals.lookup k) ∧ t'.code = t.code ∧
      HeapFrame s0 t' ∧ evaluateHOLFiniteState t' rest = (some (.returned v), output) ∧ post.globals = output.globals := by
  obtain ⟨⟨H, heap, hb, ha⟩, other⟩ := frame
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
  have body := evaluate_decodeBytesList_body entry P L LIM MAXB H (by rw [← hentry]; exact code)
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n1, n2, n3])
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n4, n5])
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n6])
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (by rw [← hentry]; exact heap) hb
  rw [bodyRun] at body
  have contract := body.2.2.2.2 value rfl
  obtain ⟨H', h1, h2, h3, h4⟩ := decodeBytesList_returned_heap_aligned entry bodyPost P L LIM MAXB H value
    (by rw [← hentry]; exact heap) hb ha contract
  have mt := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_bytes_list)
  rw [bodyRun] at mt
  refine ⟨setVarHOLFinite name value {bodyPost with locals := t.locals}, output, fun k hk => ?_, ?_, ⟨⟨H', h1, h2, h3⟩,
    fun k hk => ?_⟩, tail, by rw [postEq]⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · show bodyPost.code = t.code; rw [mt.1, ← hentry]; rfl
  · show bodyPost.globals.lookup k = s0.globals.lookup k
    rw [h4 k hk, ← hentry]; exact other k hk

#print axioms ret_bytesListDecl
end InitECandidate.Runtime
