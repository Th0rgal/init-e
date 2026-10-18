import InitECandidate.Runtime.StatelessPayloadSuffixReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem ret_bytesListDecl_heap {F : Type} (t post : PanSemStateFiniteExact 64 F) (name : MlS) (args : List (ExpHOL 64))
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
      HeapGrow Hc t t' ∧
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
  obtain ⟨H', h1, h2, h3, h4, h5⟩ := sszSplitReturned_heap_grow _ splitPost L LIM Hc value
    (by rw [← hentry]; exact heap) hb ha ret
  have mt := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_bytes_list)
  rw [bodyRun] at mt
  subst hv
  refine ⟨setVarHOLFinite name (.rStruct [.val (.word arr), .val (.word cnt)]) {bodyPost with locals := t.locals},
    output, arr, cnt, fun k hk => ?_, ?_, ?_, ⟨H', ?_, h2, h3, h4, fun k hk => ?_⟩, tail, by rw [postEq],
    by rw [postEq]⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.code = t.code; rw [mt.1, ← hentry]; rfl
  · show bodyPost.globals.lookup _ = _; rw [og]; exact h1
  · show bodyPost.globals.lookup k = t.globals.lookup k; rw [og, h5 k hk, ← hentry]; rfl

#print axioms ret_bytesListDecl_heap

/-- Final heap pointer of a returned witness suffix from At35 is at least the entry heap. -/
theorem witness35_heap {F : Type} (E out : PanSemStateFiniteExact 64 F) (WP WL S offsets Hc : BitVec 64)
    (v : ValueHOL 64) (code : E.code = originalRuntimeCode) (loc : WLocals E WP WL S)
    (hg : E.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : E.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc)))
    (hb : Hc.toNat ≤ 33806089496) (ha : Hc.toNat % 8 = 0)
    (run : evaluateHOLFiniteState E (statelessAt 35) = (some (.returned v), out)) :
    ∃ Hf : BitVec 64, out.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ Hc.toNat ≤ Hf.toNat := by
  have wn := witness_names
  simp only [ne_eq] at wn
  obtain ⟨hwp, hwl, hsi⟩ := loc
  rw [source_stateless_witness_check] at run
  obtain ⟨t1, r1, l1, g1, c1⟩ := ret_checkCall E out _ offsets WL v code hg hwl run
  rw [source_stateless_witness_load0] at r1
  obtain ⟨val0, o1, init0, r2, e2⟩ := evaluate_dec_returned_scope t1 out (ofString "w0") .one _ _ v r1
  obtain ⟨A0, rfl⟩ := eval_load_one_word t1 _ val0 init0
  rw [source_stateless_witness_load1] at r2
  obtain ⟨val1, o2, init1, r3, e3⟩ := evaluate_dec_returned_scope _ o1 (ofString "w1") .one _ _ v r2
  obtain ⟨A1, rfl⟩ := eval_load_one_word _ _ val1 init1
  rw [source_stateless_witness_load2] at r3
  obtain ⟨val2, o3, init2, r4, e4⟩ := evaluate_dec_returned_scope _ o2 (ofString "w2") .one _ _ v r3
  obtain ⟨A2, rfl⟩ := eval_load_one_word _ _ val2 init2
  generalize ht4 : setVarHOLFinite (ofString "w2") (.val (.word A2)) (setVarHOLFinite (ofString "w1") (.val (.word A1))
    (setVarHOLFinite (ofString "w0") (.val (.word A0)) t1)) = t4 at r4
  have t4l : ∀ k, k ≠ ofString "w0" → k ≠ ofString "w1" → k ≠ ofString "w2" → t4.locals.lookup k = E.locals.lookup k := by
    intro k a b c; rw [← ht4, ← l1]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wn, Ne.symm a, Ne.symm b, Ne.symm c]
  have t4w0 : t4.locals.lookup (ofString "w0") = some (.val (.word A0)) := by rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wn]
  have t4w1 : t4.locals.lookup (ofString "w1") = some (.val (.word A1)) := by rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wn]
  have t4w2 : t4.locals.lookup (ofString "w2") = some (.val (.word A2)) := by rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wn]
  have t4wp := (t4l _ (by simp [wn]) (by simp [wn]) (by simp [wn])).trans hwp
  have t4wl := (t4l _ (by simp [wn]) (by simp [wn]) (by simp [wn])).trans hwl
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact c1.trans code
  have t4g : t4.globals = E.globals := by rw [← ht4]; exact g1
  rw [source_stateless_first_witness] at r4
  have args4 : evalListHOLFinite t4 (h := fun address => Classical.propDecidable (t4.memaddrs address))
      statelessFirstWitnessArguments = some [.val (.word (WP + A0)), .val (.word (A1 - A0)),
        .val (.word 9223372036854775807), .val (.word 1024)] := by
    simp [statelessFirstWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, t4wp, t4w0, t4w1,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t5, o5, _, _, k5, _, cd5, ⟨H1, hh1, g1H, b1, al1, _⟩, r5, g5, _⟩ :=
    ret_bytesListDecl_heap t4 o3 (ofString "st0") _ _ _ _ _ _ Hc v t4c args4 (by rw [t4g]; exact heap) hb ha r4
  rw [source_stateless_witness_store40] at r5
  obtain ⟨M5, r6⟩ := ret_storeSeq _ _ _ _ _ v r5
  rw [source_stateless_witness_store41] at r6
  obtain ⟨M6, r7⟩ := ret_storeSeq _ _ _ _ _ v r6
  generalize ht7 : ({({t5 with memory := M5} : PanSemStateFiniteExact 64 F) with memory := M6} :
    PanSemStateFiniteExact 64 F) = t7 at r7
  have t7l : ∀ k, k ≠ ofString "st0" → t7.locals.lookup k = t4.locals.lookup k := by
    intro k hk; rw [← ht7]; exact k5 k hk
  have t7c : t7.code = originalRuntimeCode := by rw [← ht7]; exact cd5.trans t4c
  have t7g : t7.globals = t5.globals := by rw [← ht7]
  have t7wp := (t7l (ofString "wp") (by simp [wn])).trans t4wp
  have t7w1 := (t7l (ofString "w1") (by simp [wn])).trans t4w1
  have t7w2 := (t7l (ofString "w2") (by simp [wn])).trans t4w2
  rw [source_stateless_middle_witness] at r7
  have args7 : evalListHOLFinite t7 (h := fun address => Classical.propDecidable (t7.memaddrs address))
      statelessMiddleWitnessArguments = some [.val (.word (WP + A1)), .val (.word (A2 - A1)),
        .val (.word 9223372036854775807), .val (.word 65536)] := by
    simp [statelessMiddleWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact,
      t7wp, t7w1, t7w2, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t8, o8, _, _, k8, _, cd8, ⟨H2, hh2, g2H, b2, al2, _⟩, r8, g8, _⟩ :=
    ret_bytesListDecl_heap t7 o5 (ofString "cd") _ _ _ _ _ _ H1 v t7c args7 (by rw [t7g]; exact hh1) b1 al1 r7
  rw [source_stateless_witness_store43] at r8
  obtain ⟨M8, r9⟩ := ret_storeSeq _ _ _ _ _ v r8
  rw [source_stateless_witness_store44] at r9
  obtain ⟨M9, r10⟩ := ret_storeSeq _ _ _ _ _ v r9
  generalize ht10 : ({({t8 with memory := M8} : PanSemStateFiniteExact 64 F) with memory := M9} :
    PanSemStateFiniteExact 64 F) = t10 at r10
  have t10l : ∀ k, k ≠ ofString "st0" → k ≠ ofString "cd" → t10.locals.lookup k = t4.locals.lookup k := by
    intro k a b; rw [← ht10]; exact (k8 k b).trans (t7l k a)
  have t10c : t10.code = originalRuntimeCode := by rw [← ht10]; exact cd8.trans t7c
  have t10g : t10.globals = t8.globals := by rw [← ht10]
  have t10wp := (t10l (ofString "wp") (by simp [wn]) (by simp [wn])).trans t4wp
  have t10wl := (t10l (ofString "wlen") (by simp [wn]) (by simp [wn])).trans t4wl
  have t10w2 := (t10l (ofString "w2") (by simp [wn]) (by simp [wn])).trans t4w2
  rw [source_stateless_last_witness] at r10
  have args10 : evalListHOLFinite t10 (h := fun address => Classical.propDecidable (t10.memaddrs address))
      statelessLastWitnessArguments = some [.val (.word (WP + A2)), .val (.word (WL - A2)),
        .val (.word 256), .val (.word 1024)] := by
    simp [statelessLastWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact,
      t10wp, t10wl, t10w2, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t11, o11, _, _, k11, _, _, ⟨H3, hh3, g3H, _, _, _⟩, r11, g11, _⟩ :=
    ret_bytesListDecl_heap t10 o8 (ofString "hd") _ _ _ _ _ _ H2 v t10c args10 (by rw [t10g]; exact hh2) b2 al2 r10
  have t11si : t11.locals.lookup (ofString "si") = some (.val (.word S)) :=
    (k11 (ofString "si") (by simp [wn])).trans ((t10l (ofString "si") (by simp [wn]) (by simp [wn])).trans ((t4l _ (by simp [wn]) (by simp [wn]) (by simp [wn])).trans hsi))
  rw [source_stateless_witness_store46] at r11
  obtain ⟨M11, r12⟩ := ret_storeSeq _ _ _ _ _ v r11
  rw [source_stateless_witness_store47] at r12
  obtain ⟨M12, r13⟩ := ret_storeSeq _ _ _ _ _ v r12
  generalize ht13 : ({({t11 with memory := M11} : PanSemStateFiniteExact 64 F) with memory := M12} :
    PanSemStateFiniteExact 64 F) = t13 at r13
  have t13si : t13.locals.lookup (ofString "si") = some (.val (.word S)) := by rw [← ht13]; exact t11si
  have t13g : t13.globals = t11.globals := by rw [← ht13]
  rw [source_stateless_witness_return, evaluateHOLFiniteState_return] at r13
  simp only [evalHOLExact, lookupKvarHOLExact, t13si] at r13
  simp [shapeOfHOLExact] at r13
  obtain ⟨_, rfl⟩ := r13
  have og : out.globals = t13.globals := by
    rw [e2]; show o1.globals = _; rw [e3]; show o2.globals = _; rw [e4]; show o3.globals = _
    rw [g5, g8, g11]; rfl
  exact ⟨H3, by rw [og, t13g]; exact hh3, by omega⟩

#print axioms witness35_heap

theorem stateless_witness_heap {F : Type} (s post : PanSemStateFiniteExact 64 F) (WP WL S offsets H : BitVec 64)
    (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hwp : s.locals.lookup (ofString "wp") = some (.val (.word WP)))
    (hwl : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (hsi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (heapBound : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (run : evaluateHOLFiniteState s (statelessAt 32) = (some (.returned v), post)) :
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat ≤ Hf.toNat := by
  rcases evaluate_stateless_witness_setup s WL offsets code hwl hg with ⟨E, W0, W1, W2, entry, eq⟩ | ⟨x, h1, h2, _⟩
  · rw [eq] at run
    obtain ⟨_, _, others, eg, _, ec, _⟩ := entry
    cases hE : evaluateHOLFiniteState E (statelessAt 35) with
    | mk r o =>
      rw [hE] at run
      obtain ⟨r1, r2⟩ := Prod.mk.inj run
      dsimp only at r1 r2
      subst r1
      have iwp : ofString "wp" ≠ ofString "i" := by decide_cbv
      have iwl : ofString "wlen" ≠ ofString "i" := by decide_cbv
      have isi : ofString "si" ≠ ofString "i" := by decide_cbv
      obtain ⟨Hf, h1, h2⟩ := witness35_heap E o WP WL S offsets H v (by rw [ec]; exact code)
        ⟨(others _ iwp).trans hwp, (others _ iwl).trans hwl, (others _ isi).trans hsi⟩
        (by rw [eg]; exact hg) (by rw [eg]; exact heap) heapBound aligned hE
      exact ⟨Hf, by rw [← r2]; exact h1, h2⟩
  · rw [run] at h1
    exact absurd (Option.some.inj h1).symm (h2 v)


theorem stateless_request_heap {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat ≤ Hf.toNat := by
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
  obtain ⟨Hf, hf1, hf2⟩ := stateless_witness_heap t4 o4 _ _ S offsets H1 v t4c t4wp t4wl t4si t4off
    t4heap b1 a1 r4
  have og : post.globals = o4.globals := by
    rw [pg1, e3]; show o3.globals = _; rw [e4]
  exact ⟨Hf, by rw [og]; exact hf1, by omega⟩

theorem stateless_hash_heap {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (NP NL OVH ORQ P L OW S offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hnp : t.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : t.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (hovh : t.locals.lookup (ofString "o_vh") = some (.val (.word OVH)))
    (horq : t.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : t.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (run : evaluateHOLFiniteState t (statelessAt 24) = (some (.returned v), post)) :
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat ≤ Hf.toNat := by
  have run' : evaluateHOLFiniteState t (reqCount "nvh" "o_rq" "o_vh" 32 (statelessAt 25)) = (some (.returned v), post) := by
    rw [← run, source_stateless_hash_count]; rfl
  obtain ⟨mod, t1, out1, ⟨m1, g1, d1, c1, k1, n1⟩, r1, pm1, pg1, _⟩ :=
    reqCount_returned t post "nvh" "o_rq" "o_vh" 32 (statelessAt 25) ORQ OVH v horq hovh code (by decide) run'
  have nv : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      ofString n ≠ ofString "nvh" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide_cbv
  have t1np := (k1 _ (nv "np" (by simp))).trans hnp
  have t1nlen := (k1 _ (nv "nlen" (by simp))).trans hnlen
  have t1ovh := (k1 _ (nv "o_vh" (by simp))).trans hovh
  have t1orq := (k1 _ (nv "o_rq" (by simp))).trans horq
  have t1p := (k1 _ (nv "p" (by simp))).trans hp
  have t1len := (k1 _ (nv "len" (by simp))).trans hlen
  have t1ow := (k1 _ (nv "o_wit" (by simp))).trans howit
  have t1si := (k1 _ (nv "si" (by simp))).trans hsi
  obtain ⟨a25, a26, a27⟩ := source_stateless_hash_stores_exact
  rw [a25] at r1
  obtain ⟨dom8, r2⟩ := seqStore_returned_exact t1 out1 _ _ _ (S + 8) (NP + OVH) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, evalListHOLExact, t1np, t1ovh, wordOpHOL, wordOp, valueIsWord, valueWord]) r1
  rw [a26] at r2
  obtain ⟨dom16, r3⟩ := seqStore_returned_exact _ out1 _ _ _ (S + 16) ((ORQ - OVH) / 32) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, n1]) r2
  rw [a27] at r3
  obtain ⟨dom24, r4⟩ := seqStore_returned_exact _ out1 _ _ _ (S + 24) (NP + 8) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, evalListHOLExact, t1np, wordOpHOL, wordOp, valueIsWord, valueWord]) r3
  generalize ht4 : ({({({t1 with memory := wmem t1.memory (S + 8) (NP + OVH)} : PanSemStateFiniteExact 64 F) with
    memory := wmem (wmem t1.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)} : PanSemStateFiniteExact 64 F) with
    memory := wmem (wmem (wmem t1.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)) (S + 24) (NP + 8)} :
      PanSemStateFiniteExact 64 F) = t4 at r4
  have t4l : t4.locals = t1.locals := by rw [← ht4]
  have t4g : t4.globals = t.globals := by rw [← ht4]; exact g1
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact c1.trans code
  have t4m : t4.memory = wmem (wmem (wmem t.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)) (S + 24) (NP + 8) := by
    rw [← ht4, m1]
  obtain ⟨Hf, hf1, hf2⟩ := stateless_request_heap t4 out1 NP NL ORQ P L OW S offsets H v t4c
    (by rw [t4l]; exact t1np) (by rw [t4l]; exact t1nlen) (by rw [t4l]; exact t1orq) (by rw [t4l]; exact t1p)
    (by rw [t4l]; exact t1len) (by rw [t4l]; exact t1ow) (by rw [t4l]; exact t1si) (by rw [t4g]; exact hg)
    (by rw [t4g]; exact heap) hb ha r4
  exact ⟨Hf, by rw [pg1]; exact hf1, hf2⟩

#print axioms stateless_hash_heap

theorem stateless_payload_suffix_final_heap {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat + 136 ≤ Hf.toNat ∧
      ∀ array count : BitVec 64, post.memory (H + 32) = .word array → post.memory (H + 40) = .word count →
        array.toNat + count.toNat * 16 ≤ Hf.toNat := by
  have nl : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      ofString n ≠ ofString "pl" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide_cbv
  rw [source_stateless_payload_call] at run
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessPayloadArguments = some [.val (.word (NP + OPL)), .val (.word (OVH - OPL))] := by
    simp [statelessPayloadArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hnp, hopl, hovh, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t1, o1, nH, arr, cnt, m32, m40, cntB, arrB, slices1, above1, k1, pl1, c1, d1, long, m0, m8, nh1, nb1, na1, grow1, g1, frame1, r1, pg1, pm1, _⟩ :=
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
  obtain ⟨Hg, hg1, hg2⟩ := stateless_hash_heap t2 o1 NP NL OVH ORQ P L OW S offsets nH v t2c
    (by rw [t2l]; exact (k "np" (by simp)).trans hnp) (by rw [t2l]; exact (k "nlen" (by simp)).trans hnlen)
    (by rw [t2l]; exact (k "o_vh" (by simp)).trans hovh) (by rw [t2l]; exact (k "o_rq" (by simp)).trans horq)
    (by rw [t2l]; exact (k "p" (by simp)).trans hp) (by rw [t2l]; exact (k "len" (by simp)).trans hlen)
    (by rw [t2l]; exact (k "o_wit" (by simp)).trans howit) (by rw [t2l]; exact (k "si" (by simp)).trans hsi)
    (by rw [t2g, g1 _ (Ne.symm hs)]; exact hg) (by rw [t2g]; exact nh1) nb1 na1 r2
  refine ⟨Hg, by rw [pg1]; exact hg1, by omega, fun array count h32 h40 => ?_⟩
  have e32 : post.memory (H + 32) = .word arr := by
    rw [pm1, keepH 32 (by decide), t2m]; simp only [wmem, if_neg (Ne.symm (neSH 32 (by decide)))]; exact m32
  have e40 : post.memory (H + 40) = .word cnt := by
    rw [pm1, keepH 40 (by decide), t2m]; simp only [wmem, if_neg (Ne.symm (neSH 40 (by decide)))]; exact m40
  rw [e32] at h32; rw [e40] at h40
  injection h32 with a; injection h40 with b
  subst a; subst b
  omega

#print axioms stateless_payload_suffix_final_heap
end InitECandidate.Runtime
