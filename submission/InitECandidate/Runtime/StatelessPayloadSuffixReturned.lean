import InitECandidate.Runtime.StatelessHashRequestWitnessReturned
import InitECandidate.Runtime.PayloadBodyReturnedBelow
import InitECandidate.Runtime.PayloadBodyReturnedValue
import InitECandidate.Runtime.StatelessPayloadCallBound
import InitECandidate.Runtime.StatelessPayloadStoreBound
import InitECandidate.Runtime.OriginalDecodePayloadCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Facts of a returned actual decode_payload declaration, before its continuation. -/
theorem ret_payloadDecl {F : Type} (t post : PanSemStateFiniteExact 64 F) (name : MlS) (args : List (ExpHOL 64))
    (rest : ProgHOL 64) (A B offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hargs : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address)) args =
      some [.val (.word A), .val (.word B)])
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (heapArena : ∀ a : BitVec 64, H.toNat ≤ a.toNat → a.toNat < 33806089496 → t.memaddrs a)
    (scratchDom : t.memaddrs (offsets + 0) ∧ t.memaddrs (offsets + 8) ∧ t.memaddrs (offsets + 16) ∧
      t.memaddrs (offsets + 24))
    (scratchBelow : offsets.toNat + 32 ≤ H.toNat) (inputFits : A.toNat + B.toNat < 2 ^ 64)
    (run : evaluateHOLFiniteState t (.decCall name .one (ofString "decode_payload") args rest) =
      (some (.returned v), post)) :
    ∃ (t1 output : PanSemStateFiniteExact 64 F) (nextHeap array count : BitVec 64),
      t1.memory (H + 32) = .word array ∧ t1.memory (H + 40) = .word count ∧
      count.toNat ≤ B.toNat / 4 ∧ array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧
      (∀ k, k ≠ name → t1.locals.lookup k = t.locals.lookup k) ∧
      t1.locals.lookup name = some (.val (.word H)) ∧ t1.code = t.code ∧ t1.memaddrs = t.memaddrs ∧
      540 ≤ B.toNat ∧ t1.memory (H + 0) = .word A ∧ t1.memory (H + 8) = .word B ∧
      t1.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧ H.toNat + 136 ≤ nextHeap.toNat ∧
      (∀ k, k ≠ ofString "heap_ptr" → t1.globals.lookup k = t.globals.lookup k) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → w ≠ offsets → w ≠ offsets + 8 → w ≠ offsets + 16 → w ≠ offsets + 24 →
        t1.memory w = t.memory w) ∧
      evaluateHOLFiniteState t1 rest = (some (.returned v), output) ∧ post.globals = output.globals ∧
      post.memory = output.memory ∧ post.memaddrs = output.memaddrs := by
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
  have hd : ∀ c : BitVec 64, c.toNat ≤ 40 → e.memaddrs (H + c) := by
    intro c hc; rw [ed]; apply heapArena <;> rw [BitVec.toNat_add] <;> omega
  have hv := payload_body_returned_value e bodyPost A B offsets H value ep el (by rw [eg]; exact hg)
    (by rw [eg]; exact heap) hb ha inputFits (by rw [ed]; exact scratchDom.1) (by rw [ed]; exact scratchDom.2.1)
    (by rw [ed]; exact scratchDom.2.2.1) (by rw [ed]; exact scratchDom.2.2.2) (hd 0 (by decide)) (hd 8 (by decide))
    (hd 16 (by decide)) (hd 24 (by decide)) (hd 32 (by decide)) (hd 40 (by decide)) ec bodyRun
  subst hv
  obtain ⟨long, array, count, nextHeap, _, countBound, read32, read40, nextGlobal, nextBound, nextAligned, growth, arrayBefore⟩ :=
    payload_body_returned_slices e bodyPost A B offsets H _ ep el (by rw [eg]; exact hg)
      (by rw [eg]; exact heap) hb ha inputFits (by rw [ed]; exact scratchDom.1) (by rw [ed]; exact scratchDom.2.1)
      (by rw [ed]; exact scratchDom.2.2.1) (by rw [ed]; exact scratchDom.2.2.2) (hd 0 (by decide)) (hd 8 (by decide))
      (hd 16 (by decide)) (hd 24 (by decide)) (hd 32 (by decide)) (hd 40 (by decide)) ec bodyRun
  obtain ⟨h0, h8, gframe⟩ := payload_body_returned_header e bodyPost A B offsets H _ ep el (by rw [eg]; exact hg)
      (by rw [eg]; exact heap) hb ha scratchBelow (by rw [ed]; exact scratchDom.1) (by rw [ed]; exact scratchDom.2.1)
      (by rw [ed]; exact scratchDom.2.2.1) (by rw [ed]; exact scratchDom.2.2.2) (hd 0 (by decide)) (hd 8 (by decide))
      (hd 16 (by decide)) (hd 24 (by decide)) (hd 32 (by decide)) (hd 40 (by decide)) ec bodyRun
  have mt := evaluateHOLFiniteState_metadata e (sourceFunctionBody Guest.guestFn_decode_payload)
  rw [bodyRun] at mt
  refine ⟨setVarHOLFinite name (.val (.word H)) {bodyPost with locals := t.locals}, output, nextHeap, array, count,
    read32, read40, countBound, arrayBefore,
    fun k hk => ?_, ?_, ?_, ?_, long, h0, h8, nextGlobal, nextBound, nextAligned, growth, fun k hk => ?_,
    fun w below s0 s8 s16 s24 => ?_, tail, by rw [postEq], by rw [postEq], by rw [postEq]⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.code = t.code; rw [mt.1, ec, code]
  · show bodyPost.memaddrs = t.memaddrs; rw [mt.2.1, ed]
  · show bodyPost.globals.lookup k = t.globals.lookup k; rw [gframe k hk, eg]
  · show bodyPost.memory w = t.memory w
    rw [payload_body_returned_below e bodyPost A B offsets H w _ ep el (by rw [eg]; exact hg)
      (by rw [eg]; exact heap) hb ha (by rw [ed]; exact scratchDom.1) (by rw [ed]; exact scratchDom.2.1)
      (by rw [ed]; exact scratchDom.2.2.1) (by rw [ed]; exact scratchDom.2.2.2) (hd 0 (by decide)) (hd 8 (by decide))
      (hd 16 (by decide)) (hd 24 (by decide)) (hd 32 (by decide)) (hd 40 (by decide)) below ⟨s0, s8, s16, s24⟩ ec
      bodyRun, em]

#print axioms ret_payloadDecl

/-- Every returned run of the actual original stateless suffix At22..At48. -/
theorem stateless_payload_suffix_returned {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (NP NL OPL OVH ORQ P L OW S offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hnp : t.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : t.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (hopl : t.locals.lookup (ofString "o_pl") = some (.val (.word OPL)))
    (hovh : t.locals.lookup (ofString "o_vh") = some (.val (.word OVH)))
    (horq : t.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : t.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (heapArena : ∀ a : BitVec 64, H.toNat ≤ a.toNat → a.toNat < 33806089496 → t.memaddrs a)
    (scratchDom : t.memaddrs (offsets + 0) ∧ t.memaddrs (offsets + 8) ∧ t.memaddrs (offsets + 16) ∧
      t.memaddrs (offsets + 24))
    (scratchBelow : offsets.toNat + 40 ≤ S.toNat) (siBelow : S.toNat + 96 ≤ H.toNat)
    (payloadFits : (NP + OPL).toNat + (OVH - OPL).toNat < 2 ^ 64)
    (run : evaluateHOLFiniteState t (statelessAt 22) = (some (.returned v), post)) :
    v = .val (.word S) ∧ HeapFrame t post ∧ 540 ≤ (OVH - OPL).toNat ∧ (ORQ - OVH) % 32 = 0 ∧
      post.memory (S + 0) = .word H ∧ post.memory (H + 0) = .word (NP + OPL) ∧
      post.memory (H + 8) = .word (OVH - OPL) ∧
      post.memory (S + 8) = .word (NP + OVH) ∧ post.memory (S + 16) = .word ((ORQ - OVH) / 32) ∧
      post.memory (S + 24) = .word (NP + 8) ∧
      (∃ array count : BitVec 64, post.memory (H + 32) = .word array ∧ post.memory (H + 40) = .word count ∧
        count.toNat ≤ (OVH - OPL).toNat / 4) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → (∀ k : BitVec 64, k.toNat < 5 → w ≠ offsets + k * 8) →
        w ≠ S + 0 → w ≠ S + 8 → w ≠ S + 16 → w ≠ S + 24 → w ≠ S + 32 →
        (w ≠ S + 40 ∧ w ≠ S + 48 ∧ w ≠ S + 56 ∧ w ≠ S + 64 ∧ w ≠ S + 72 ∧ w ≠ S + 80) →
        post.memory w = t.memory w) := by
  have nl : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      ofString n ≠ ofString "pl" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide_cbv
  rw [source_stateless_payload_call] at run
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessPayloadArguments = some [.val (.word (NP + OPL)), .val (.word (OVH - OPL))] := by
    simp [statelessPayloadArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hnp, hopl, hovh, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t1, o1, nH, arr, cnt, m32, m40, cntB, arrB, k1, pl1, c1, d1, long, m0, m8, nh1, nb1, na1, grow1, g1, frame1, r1, pg1, pm1, _⟩ :=
    ret_payloadDecl t post (ofString "pl") _ _ (NP + OPL) (OVH - OPL) offsets H v code args hg heap hb ha heapArena
      scratchDom (by omega) payloadFits run
  have k : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      t1.locals.lookup (ofString n) = t.locals.lookup (ofString n) := fun n hn => k1 _ (nl n hn)
  -- si+0 store
  rw [source_stateless_payload_store] at r1
  unfold statelessPayloadStore at r1
  obtain ⟨dom0, r2⟩ := seqStore_returned_exact t1 o1 _ _ _ (S + 0) H v
    (by simp [evalHOLExact, evalListHOLExact, (k "si" (by simp)).trans hsi, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, pl1]) r1
  generalize ht2 : ({t1 with memory := wmem t1.memory (S + 0) H} : PanSemStateFiniteExact 64 F) = t2 at r2
  have t2l : t2.locals = t1.locals := by rw [← ht2]
  have t2g : t2.globals = t1.globals := by rw [← ht2]
  have t2c : t2.code = originalRuntimeCode := by rw [← ht2]; exact c1.trans code
  have t2m : t2.memory = wmem t1.memory (S + 0) H := by rw [← ht2]
  have hs : ofString "heap_ptr" ≠ ofString "ssz_offs" := by decide_cbv
  obtain ⟨hv, ⟨⟨Hf, hf1, hf2, hf3⟩, hfo⟩, mod, frame, cells, _⟩ := stateless_hash_request_witness_returned t2 o1
    NP NL OVH ORQ P L OW S offsets nH v t2c
    (by rw [t2l]; exact (k "np" (by simp)).trans hnp) (by rw [t2l]; exact (k "nlen" (by simp)).trans hnlen)
    (by rw [t2l]; exact (k "o_vh" (by simp)).trans hovh) (by rw [t2l]; exact (k "o_rq" (by simp)).trans horq)
    (by rw [t2l]; exact (k "p" (by simp)).trans hp) (by rw [t2l]; exact (k "len" (by simp)).trans hlen)
    (by rw [t2l]; exact (k "o_wit" (by simp)).trans howit) (by rw [t2l]; exact (k "si" (by simp)).trans hsi)
    (by rw [t2g, g1 _ (Ne.symm hs)]; exact hg) (by rw [t2g]; exact nh1) nb1 na1 r2
  obtain ⟨c8, c16, c24⟩ := cells scratchBelow (by omega)
  have sNat : ∀ c : BitVec 64, c.toNat ≤ 80 → (S + c).toNat = S.toNat + c.toNat := by
    intro c hc; rw [BitVec.toNat_add]; omega
  have hNat : ∀ c : BitVec 64, c.toNat ≤ 40 → (H + c).toNat = H.toNat + c.toNat := by
    intro c hc; rw [BitVec.toNat_add]; omega
  have oNat : ∀ q : BitVec 64, q.toNat < 5 → (offsets + q * 8).toNat = offsets.toNat + q.toNat * 8 := by
    intro q hq; rw [BitVec.toNat_add, BitVec.toNat_mul]; simp; omega
  -- payload header cells survive the At24 suffix
  have keepH : ∀ c : BitVec 64, c.toNat ≤ 40 → o1.memory (H + c) = t2.memory (H + c) := by
    intro c hc
    apply frame
    · rw [hNat c hc]; omega
    · intro q hq e; have := congrArg BitVec.toNat e; rw [hNat c hc, oNat q hq] at this; omega
    all_goals first
      | (intro e; have := congrArg BitVec.toNat e; rw [hNat c hc, sNat _ (by decide)] at this; simp at this; omega)
      | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          · intro e; have := congrArg BitVec.toNat e; rw [hNat c hc, sNat _ (by decide)] at this; simp at this; omega)
  have keepS0 : o1.memory (S + 0) = t2.memory (S + 0) := by
    apply frame
    · rw [sNat 0 (by decide)]; simp; omega
    · intro q hq e; have := congrArg BitVec.toNat e; rw [sNat 0 (by decide), oNat q hq] at this; simp at this; omega
    all_goals first
      | (intro e; have := congrArg BitVec.toNat e; rw [sNat 0 (by decide), sNat _ (by decide)] at this; simp at this)
      | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          · intro e; have := congrArg BitVec.toNat e; rw [sNat 0 (by decide), sNat _ (by decide)] at this; simp at this)
  have neSH : ∀ c : BitVec 64, c.toNat ≤ 40 → S + 0 ≠ H + c := by
    intro c hc e; have := congrArg BitVec.toNat e; rw [sNat 0 (by decide), hNat c hc] at this; simp at this; omega
  refine ⟨hv, ⟨⟨Hf, by rw [pg1]; exact hf1, hf2, hf3⟩, fun q hq => by rw [pg1, hfo q hq, t2g, g1 q hq]⟩, long, mod,
    ?_, ?_, ?_, by rw [pm1]; exact c8, by rw [pm1]; exact c16, by rw [pm1]; exact c24, ⟨arr, cnt, ?_, ?_, cntB⟩, ?_⟩
  · rw [pm1, keepS0, t2m]; simp [wmem]
  · rw [pm1, keepH 0 (by decide), t2m]; simp only [wmem, if_neg (Ne.symm (neSH 0 (by decide)))]; exact m0
  · rw [pm1, keepH 8 (by decide), t2m]; simp only [wmem, if_neg (Ne.symm (neSH 8 (by decide)))]; exact m8
  · rw [pm1, keepH 32 (by decide), t2m]; simp only [wmem, if_neg (Ne.symm (neSH 32 (by decide)))]; exact m32
  · rw [pm1, keepH 40 (by decide), t2m]; simp only [wmem, if_neg (Ne.symm (neSH 40 (by decide)))]; exact m40
  · intro w below scratch s0 s8 s16 s24 s32 headers
    rw [pm1, frame w (by omega) scratch s8 s16 s24 s32 headers, t2m]
    simp only [wmem, if_neg s0]
    exact frame1 w below (by simpa using scratch 0 (by decide)) (by simpa using scratch 1 (by decide))
      (by simpa using scratch 2 (by decide)) (by simpa using scratch 3 (by decide))

#print axioms stateless_payload_suffix_returned
end InitECandidate.Runtime
