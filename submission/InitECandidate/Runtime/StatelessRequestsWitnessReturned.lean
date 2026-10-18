import InitECandidate.Runtime.StatelessWitnessMemFrame
import InitECandidate.Runtime.DecodeRequestsReturned
import InitECandidate.Runtime.StatelessRequestCallBound
import InitECandidate.Runtime.StatelessRequestStoreBound
import InitECandidate.Runtime.StatelessWitnessEntryBound
import InitECandidate.Runtime.PanTwoWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem reqCells_above (H w p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4 : BitVec 64) (hb : H.toNat ≤ 33806089496)
    (below : w.toNat < H.toNat) :
    ∀ x ∈ reqCellValues p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4, w ≠ H + x.1 := by
  intro x hx e
  have hx1 : x.1.toNat ≤ 72 := by
    simp only [reqCellValues, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_add] at this
  omega

/-- A returned actual decode_requests declaration: rq is the old heap pointer,
the heap grows to an aligned capped end, and watched words below the old
heap outside the five scratch cells keep their value. -/
theorem ret_requestsDecl_mem {F : Type} (t post : PanSemStateFiniteExact 64 F) (name : MlS) (args : List (ExpHOL 64))
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
      t'.locals.lookup name = some (.val (.word H)) ∧ t'.code = t.code ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → (∀ k : BitVec 64, k.toNat < 5 → w ≠ offsets + k * 8) →
        t'.memory w = t.memory w) ∧ HeapGrow H t t' ∧
      evaluateHOLFiniteState t' rest = (some (.returned v), output) ∧ post.globals = output.globals ∧
      post.memory = output.memory := by
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
  refine ⟨setVarHOLFinite name (.val (.word H)) {bodyPost with locals := t.locals}, output, fun k hk => ?_, ?_, ?_, ?_,
    ⟨allocationEnd H 80, ?_, by omega, allocationEnd_within_heap H 80 hb request, cov.2.2, fun k hk => ?_⟩,
    tail, by rw [postEq], by rw [postEq]⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.code = t.code; rw [mt.1, ← hentry]; rfl
  · intro w below scratch
    show bodyPost.memory w = t.memory w
    rw [mem, memWrites_frame _ _ _ _ (reqCells_above H w _ _ _ _ _ _ _ _ _ _ _ hb below), frame w scratch, ← hentry]
    rfl
  · show bodyPost.globals.lookup _ = _
    rw [glob]; simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.globals.lookup k = t.globals.lookup k
    rw [glob]; simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk, ← hentry]
    rfl

#print axioms ret_requestsDecl_mem

/-- Every returned run of the actual original stateless suffix At28..At48
returns si, keeps a capped aligned heap and all non-allocator globals, and
keeps every word below the At28 heap except the five scratch offset cells,
si+32 and the six witness header cells. -/
theorem stateless_request_witness_returned {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (NP NL ORQ P L OW S offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hnp : t.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : t.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (horq : t.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : t.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (run : evaluateHOLFiniteState t (statelessAt 28) = (some (.returned v), post)) :
    v = .val (.word S) ∧ HeapFrame t post ∧
      ∀ w : BitVec 64, w.toNat < H.toNat → (∀ k : BitVec 64, k.toNat < 5 → w ≠ offsets + k * 8) → w ≠ S + 32 →
        (w ≠ S + 40 ∧ w ≠ S + 48 ∧ w ≠ S + 56 ∧ w ≠ S + 64 ∧ w ≠ S + 72 ∧ w ≠ S + 80) →
        post.memory w = t.memory w := by
  have nrq : ∀ n : String, n ∈ ["si", "p", "len", "o_wit"] → ofString n ≠ ofString "rq" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl <;> decide_cbv
  rw [source_stateless_request_call] at run
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessRequestArguments = some [.val (.word (NP + ORQ)), .val (.word (NL - ORQ))] := by
    simp [statelessRequestArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hnp, hnlen, horq,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t1, o1, k1, rq1, c1, mem1, ⟨H1, hh1, g1, b1, a1, oth1⟩, r1, pg1, pm1⟩ :=
    ret_requestsDecl_mem t post (ofString "rq") _ _ (NP + ORQ) (NL - ORQ) H offsets v code args heap hg hb run
  have t1si := (k1 _ (nrq "si" (by simp))).trans hsi
  have t1p := (k1 _ (nrq "p" (by simp))).trans hp
  have t1len := (k1 _ (nrq "len" (by simp))).trans hlen
  have t1ow := (k1 _ (nrq "o_wit" (by simp))).trans howit
  -- si+32 store
  rw [source_stateless_request_store, evaluateHOLFiniteState_seq_line780] at r1
  unfold statelessRequestStore at r1
  have addr : @evalHOLExact 64 F _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
      (.op .add [.var .local (ofString "si"), .const 32]) = some (.val (.word (S + 32))) := by
    simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]
  have frame2 := fun (w : BitVec 64) (hw : w ≠ S + 32) => evaluate_wordStore_memory_frame t1 _
    (.var .local (ofString "rq")) (S + 32) w addr (fun parsed h => by simp [evalHOLExact, rq1] at h; exact ⟨_, h.symm⟩) hw
  rcases evaluate_store_cases t1 (.op .add [.var .local (ofString "si"), .const 32]) (.var .local (ofString "rq"))
    with err | ⟨M, ok⟩
  · rw [err] at r1; simp at r1
  rw [ok] at r1 frame2
  dsimp only at r1
  generalize ht2 : ({t1 with memory := M} : PanSemStateFiniteExact 64 F) = t2 at r1 frame2
  have t2l : t2.locals = t1.locals := by rw [← ht2]
  have t2g : t2.globals = t1.globals := by rw [← ht2]
  have t2c : t2.code = t1.code := by rw [← ht2]
  -- wp and wlen
  rw [source_stateless_witness_pointer] at r1
  obtain ⟨val3, o3, init3, r3, e3⟩ := evaluate_dec_returned_scope t2 o1 (ofString "wp") .one _ _ v r1
  have i3 : @evalHOLExact 64 F _ t2.toExact (fun x => Classical.propDecidable (t2.memaddrs x))
      (.op .add [.var .local (ofString "p"), .var .local (ofString "o_wit")]) = some (.val (.word (P + OW))) := by
    simp [evalHOLExact, evalListHOLExact, t2l, t1p, t1ow, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [i3] at init3
  obtain rfl := (Option.some.inj init3).symm
  rw [source_stateless_witness_length] at r3
  obtain ⟨val4, o4, init4, r4, e4⟩ := evaluate_dec_returned_scope _ o3 (ofString "wlen") .one _ _ v r3
  have wpl : ofString "len" ≠ ofString "wp" := by decide_cbv
  have wpo : ofString "o_wit" ≠ ofString "wp" := by decide_cbv
  have i4 : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "wp") (.val (.word (P + OW))) t2).toExact
      (fun x => Classical.propDecidable _)
      (.op .sub [.var .local (ofString "len"), .var .local (ofString "o_wit")]) = some (.val (.word (L - OW))) := by
    simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wpl, wpo, Ne.symm wpl, Ne.symm wpo, t2l, t1len, t1ow, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [i4] at init4
  obtain rfl := (Option.some.inj init4).symm
  generalize ht4 : setVarHOLFinite (ofString "wlen") (.val (.word (L - OW)))
    (setVarHOLFinite (ofString "wp") (.val (.word (P + OW))) t2) = t4 at r4
  have siw : ofString "si" ≠ ofString "wp" := by decide_cbv
  have siwl : ofString "si" ≠ ofString "wlen" := by decide_cbv
  have wwl : ofString "wp" ≠ ofString "wlen" := by decide_cbv
  have t4wp : t4.locals.lookup (ofString "wp") = some (.val (.word (P + OW))) := by
    rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wwl, Ne.symm wwl]
  have t4wl : t4.locals.lookup (ofString "wlen") = some (.val (.word (L - OW))) := by rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have t4si : t4.locals.lookup (ofString "si") = some (.val (.word S)) := by
    rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, siw, siwl, Ne.symm siw, Ne.symm siwl, t2l, t1si]
  have t4g : t4.globals = t1.globals := by rw [← ht4]; exact t2g
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact t2c.trans (c1.trans code)
  have t4m : ∀ w, t4.memory w = t2.memory w := by intro w; rw [← ht4]; rfl
  have hhs : ofString "heap_ptr" ≠ ofString "ssz_offs" := by decide_cbv
  have t4off : t4.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
    rw [t4g, oth1 _ (Ne.symm hhs)]; exact hg
  have t4heap : t4.globals.lookup (ofString "heap_ptr") = some (.val (.word H1)) := by rw [t4g]; exact hh1
  obtain ⟨hv, ⟨⟨Hf, hf1, hf2, hf3⟩, hfo⟩⟩ := stateless_witness_returned t4 o4 _ _ S offsets H1 v t4c t4wp t4wl t4si t4off
    t4heap b1 a1 r4
  have og : post.globals = o4.globals := by
    rw [pg1, e3]; show o3.globals = _; rw [e4]
  have om : post.memory = o4.memory := by
    rw [pm1, e3]; show o3.memory = _; rw [e4]
  refine ⟨hv, ⟨⟨Hf, by rw [og]; exact hf1, hf2, hf3⟩, fun k hk => ?_⟩, ?_⟩
  · rw [og, hfo k hk, t4g, oth1 k hk]
  · intro w below scratch s32 headers
    have wmem := stateless_witness_returned_memory t4 o4 _ _ S offsets H1 w v t4c t4wp t4wl t4si t4off t4heap b1 a1
      (by omega) ⟨by simpa using scratch 0 (by decide), by simpa using scratch 1 (by decide),
        by simpa using scratch 2 (by decide)⟩ headers r4
    rw [om, wmem, t4m, frame2 w s32, mem1 w below scratch]

#print axioms stateless_request_witness_returned
end InitECandidate.Runtime
