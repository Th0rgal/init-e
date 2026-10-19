import InitECandidate.Runtime.StatelessRequestsWitnessReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual request-decoder declaration also exposes unchanged address
domains at its continuation and after outer local restoration. -/
theorem ret_requestsDecl_mem_domain {F : Type} (t post : PanSemStateFiniteExact 64 F) (name : MlS) (args : List (ExpHOL 64))
    (rest : ProgHOL 64) (A B H offsets : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hargs : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address)) args =
      some [.val (.word A), .val (.word B)])
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hb : H.toNat ≤ 33806089496)
    (run : evaluateHOLFiniteState t (.decCall name .one (ofString "decode_requests") args rest) =
      (some (.returned v), post)) :
    ∃ t' output : PanSemStateFiniteExact 64 F,
      (∀ k, k ≠ name → t'.locals.lookup k = t.locals.lookup k) ∧
      t'.locals.lookup name = some (.val (.word H)) ∧ t'.code = t.code ∧ t'.memaddrs = t.memaddrs ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → (∀ k : BitVec 64, k.toNat < 5 → w ≠ offsets + k * 8) →
        t'.memory w = t.memory w) ∧ HeapGrow H t t' ∧
      evaluateHOLFiniteState t' rest = (some (.returned v), output) ∧ post.globals = output.globals ∧
      post.memory = output.memory ∧ post.memaddrs = output.memaddrs := by
  have pl : ofString "p" ≠ ofString "len" := by decide_cbv
  have lookup := pan_two_word_lookup_shape t.code.lookup (ofString "decode_requests") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_requests) .one A B pl
    (by rw [code]; exact originalRuntimeCode_decodeRequests_lookup)
  obtain ⟨value, bodyPost, output, bodyRun, _, tail, postEq⟩ := evaluate_decCall_checked_returned_exact_scope t post
    name (ofString "decode_requests") .one .one args _ _ rest _ v hargs lookup run
  generalize hentry : callEntryStateHOLFinite t ((HolFiniteMapExact.empty.update (ofString "p", .val (.word A))).update
    (ofString "len", .val (.word B))) = entry at bodyRun
  have contract := evaluate_decodeRequests_returned entry A B H offsets (by rw [← hentry]; exact code)
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm pl])
    (by rw [← hentry]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (by rw [← hentry]; exact heap) hb (by rw [← hentry]; exact hg) value (by rw [bodyRun])
  rw [bodyRun] at contract
  obtain ⟨_, M1, frame, _, facts⟩ := contract
  dsimp only [ReqArrayFacts] at facts
  obtain ⟨request, hv, _, _, _, _, _, _, _, _, _, _, _, mem, glob, _⟩ := facts
  subst hv
  have mt := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_requests)
  rw [bodyRun] at mt
  have sum := allocationGuard_sum_bound H 80 hb request
  have cov := allocationEnd_covers H 80 sum
  refine ⟨setVarHOLFinite name (.val (.word H)) {bodyPost with locals := t.locals}, output, fun k hk => ?_, ?_, ?_, ?_, ?_,
    ⟨allocationEnd H 80, ?_, by omega, allocationEnd_within_heap H 80 hb request, cov.2.2, fun k hk => ?_⟩,
    tail, by rw [postEq], by rw [postEq], by rw [postEq]⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.code = t.code; rw [mt.1, ← hentry]; rfl
  · show bodyPost.memaddrs = t.memaddrs; rw [mt.2.1, ← hentry]; rfl
  · intro w below scratch
    show bodyPost.memory w = t.memory w
    rw [mem, memWrites_frame _ _ _ _ (reqCells_above H w _ _ _ _ _ _ _ _ _ _ _ hb below), frame w scratch, ← hentry]
    rfl
  · show bodyPost.globals.lookup _ = _
    rw [glob]; simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.globals.lookup k = t.globals.lookup k
    rw [glob]; simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk, ← hentry]
    rfl


#print axioms ret_requestsDecl_mem_domain
end InitECandidate.Runtime
