import InitECandidate.Runtime.StatelessWitnessReturned
import InitECandidate.Runtime.PayloadSplitHeaderFrame
import InitECandidate.Runtime.WordStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem sszSplitReturned_heap_grow {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length limit heapPointer : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (returned : SszSplitVarListReturned state length limit heapPointer value post) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      heapPointer.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      ∀ key, key ≠ ofString "heap_ptr" → post.globals.lookup key = state.globals.lookup key := by
  rcases returned with ⟨_,_,globals⟩ | ⟨_,first,_,_,_,_,request,globals⟩
  · refine ⟨heapPointer,?_,le_refl _,heapBound,aligned,?_⟩
    · rw [globals]; exact heap
    · intro key different; rw [globals]
  · have sum := allocationGuard_sum_bound heapPointer _ heapBound request
    have cov := allocationEnd_covers _ _ sum
    refine ⟨allocationEnd heapPointer ((first >>> (2 : Nat)) * 16),?_, by omega,
      allocationEnd_within_heap heapPointer _ heapBound request, cov.2.2, ?_⟩
    · rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro key different
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

/-- Heap facts relative to the current state, with growth. -/
def HeapGrow {F : Type} (Hc : BitVec 64) (t t' : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ H' : BitVec 64, t'.globals.lookup (ofString "heap_ptr") = some (.val (.word H')) ∧ Hc.toNat ≤ H'.toNat ∧
    H'.toNat ≤ 33806089496 ∧ H'.toNat % 8 = 0 ∧
    ∀ k, k ≠ ofString "heap_ptr" → t'.globals.lookup k = t.globals.lookup k

theorem ret_bytesListDecl_mem {F : Type} (t post : PanSemStateFiniteExact 64 F) (name : MlS) (args : List (ExpHOL 64))
    (rest : ProgHOL 64) (P L LIM MAXB Hc w : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hargs : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address)) args =
      some [.val (.word P), .val (.word L), .val (.word LIM), .val (.word MAXB)])
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc)))
    (hb : Hc.toNat ≤ 33806089496) (ha : Hc.toNat % 8 = 0) (below : w.toNat < Hc.toNat)
    (run : evaluateHOLFiniteState t (.decCall name (.comb [.one,.one]) (ofString "decode_bytes_list") args rest) =
      (some (.returned v), post)) :
    ∃ (t' output : PanSemStateFiniteExact 64 F) (arr cnt : BitVec 64),
      (∀ k, k ≠ name → t'.locals.lookup k = t.locals.lookup k) ∧
      t'.locals.lookup name = some (.rStruct [.val (.word arr), .val (.word cnt)]) ∧ t'.code = t.code ∧
      t'.memory w = t.memory w ∧ HeapGrow Hc t t' ∧
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
  obtain ⟨clock, splitPost, _, ret, slices, om, og, _, _⟩ := body.2.2.2.2 value rfl
  obtain ⟨arr, cnt, hv, _, _⟩ := sszSplitReturned_count _ _ _ _ _ value ret
  obtain ⟨H', h1, h2, h3, h4, h5⟩ := sszSplitReturned_heap_grow _ splitPost L LIM Hc value
    (by rw [← hentry]; exact heap) hb ha ret
  have frame := sszSlices_frame_below _ P L Hc w splitPost slices hb below
  have mt := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_bytes_list)
  rw [bodyRun] at mt
  subst hv
  refine ⟨setVarHOLFinite name (.rStruct [.val (.word arr), .val (.word cnt)]) {bodyPost with locals := t.locals},
    output, arr, cnt, fun k hk => ?_, ?_, ?_, ?_, ⟨H', ?_, h2, h3, h4, fun k hk => ?_⟩, tail, by rw [postEq],
    by rw [postEq]⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · show bodyPost.code = t.code; rw [mt.1, ← hentry]; rfl
  · show bodyPost.memory w = t.memory w; rw [om, frame, ← hentry]; rfl
  · show bodyPost.globals.lookup _ = _; rw [og]; exact h1
  · show bodyPost.globals.lookup k = t.globals.lookup k; rw [og, h5 k hk, ← hentry]; rfl

#print axioms ret_bytesListDecl_mem

theorem ret_siStore_mem {F : Type} (t post : PanSemStateFiniteExact 64 F) (off : BitVec 64) (fld : Nat) (var : String)
    (rest : ProgHOL 64) (S a c w : BitVec 64) (v : ValueHOL 64) (hfld : fld = 0 ∨ fld = 1)
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hvar : t.locals.lookup (ofString var) = some (.rStruct [.val (.word a), .val (.word c)]))
    (hw : w ≠ S + off)
    (run : evaluateHOLFiniteState t (.seq (.store (.op .add [.var .local (ofString "si"), .const off])
      (.rfield fld (.var .local (ofString var)))) rest) = (some (.returned v), post)) :
    ∃ t' : PanSemStateFiniteExact 64 F, t'.memory w = t.memory w ∧ t'.locals = t.locals ∧ t'.globals = t.globals ∧
      t'.code = t.code ∧ evaluateHOLFiniteState t' rest = (some (.returned v), post) := by
  have addr : @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x))
      (.op .add [.var .local (ofString "si"), .const off]) = some (.val (.word (S + off))) := by
    simp [evalHOLExact, evalListHOLExact, hsi, wordOpHOL, wordOp, valueIsWord, valueWord]
  have frame := evaluate_wordStore_memory_frame t _ (.rfield fld (.var .local (ofString var))) (S + off) w addr
    (fun parsed h => by
      rcases hfld with rfl | rfl <;> simp [evalHOLExact, hvar] at h <;> exact ⟨_, h.symm⟩) hw
  rw [evaluateHOLFiniteState_seq_line780] at run
  rcases evaluate_store_cases t (.op .add [.var .local (ofString "si"), .const off])
    (.rfield fld (.var .local (ofString var))) with err | ⟨M, ok⟩
  · rw [err] at run; simp at run
  · rw [ok] at run frame
    exact ⟨_, frame, rfl, rfl, rfl, run⟩

theorem ret_checkCall_mem {F : Type} (t post : PanSemStateFiniteExact 64 F) (rest : ProgHOL 64) (offsets WL : BitVec 64)
    (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hwl : t.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (run : evaluateHOLFiniteState t (.seq statelessWitnessCheckCall rest) = (some (.returned v), post)) :
    ∃ t', evaluateHOLFiniteState t' rest = (some (.returned v), post) ∧ t'.locals = t.locals ∧
      t'.globals = t.globals ∧ t'.code = t.code ∧ t'.memory = t.memory := by
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
      obtain ⟨_, em, eg, _, el⟩ := sszCheckOffsets_call_returned t _ offsets 3 12 WL args code (by decide) t'
        (by unfold statelessWitnessCheckCall at callRun; exact callRun)
      have mt := evaluateHOLFiniteState_metadata t statelessWitnessCheckCall
      rw [callRun] at mt
      exact ⟨t', run, el, eg, mt.1, em⟩

/-- Watched-word frame of the actual witness suffix At35..At48. -/
theorem witness35_memory {F : Type} (E out : PanSemStateFiniteExact 64 F) (WP WL S offsets Hc w : BitVec 64)
    (v : ValueHOL 64) (code : E.code = originalRuntimeCode) (loc : WLocals E WP WL S)
    (hg : E.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : E.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc)))
    (hb : Hc.toNat ≤ 33806089496) (ha : Hc.toNat % 8 = 0) (below : w.toNat < Hc.toNat)
    (sep : w ≠ S + 40 ∧ w ≠ S + 48 ∧ w ≠ S + 56 ∧ w ≠ S + 64 ∧ w ≠ S + 72 ∧ w ≠ S + 80)
    (run : evaluateHOLFiniteState E (statelessAt 35) = (some (.returned v), out)) :
    out.memory w = E.memory w := by
  have wn := witness_names
  simp only [ne_eq] at wn
  obtain ⟨hwp, hwl, hsi⟩ := loc
  obtain ⟨s40, s48, s56, s64, s72, s80⟩ := sep
  rw [source_stateless_witness_check] at run
  obtain ⟨t1, r1, l1, g1, c1, m1⟩ := ret_checkCall_mem E out _ offsets WL v code hg hwl run
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
  have t4si := (t4l _ (by simp [wn]) (by simp [wn]) (by simp [wn])).trans hsi
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact c1.trans code
  have t4g : t4.globals = E.globals := by rw [← ht4]; exact g1
  have t4m : t4.memory w = E.memory w := by rw [← ht4]; show t1.memory w = _; rw [m1]
  rw [source_stateless_first_witness] at r4
  have args4 : evalListHOLFinite t4 (h := fun address => Classical.propDecidable (t4.memaddrs address))
      statelessFirstWitnessArguments = some [.val (.word (WP + A0)), .val (.word (A1 - A0)),
        .val (.word 9223372036854775807), .val (.word 1024)] := by
    simp [statelessFirstWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, t4wp, t4w0, t4w1,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t5, o5, a5, c5, k5, n5, cd5, m5, ⟨H1, hh1, g1H, b1, al1, oth1⟩, r5, g5, mm5⟩ :=
    ret_bytesListDecl_mem t4 o3 (ofString "st0") _ _ _ _ _ _ Hc w v t4c args4 (by rw [t4g]; exact heap) hb ha below r4
  have t5si : t5.locals.lookup (ofString "si") = some (.val (.word S)) := (k5 _ (by simp [wn])).trans t4si
  rw [source_stateless_witness_store40] at r5
  obtain ⟨u1, mu1, lu1, gu1, cu1, ru1⟩ := ret_siStore_mem t5 o5 40 0 "st0" _ S a5 c5 w v (Or.inl rfl) t5si n5 s40 r5
  rw [source_stateless_witness_store41] at ru1
  obtain ⟨t7, m7, l7, g7, c7, r7⟩ := ret_siStore_mem u1 o5 48 1 "st0" _ S a5 c5 w v (Or.inr rfl) (by rw [lu1]; exact t5si)
    (by rw [lu1]; exact n5) s48 ru1
  have t7l : ∀ k, k ≠ ofString "st0" → t7.locals.lookup k = t4.locals.lookup k := by
    intro k hk; rw [l7, lu1]; exact k5 k hk
  have t7c : t7.code = originalRuntimeCode := by rw [c7, cu1]; exact cd5.trans t4c
  have t7wp := (t7l (ofString "wp") (by simp [wn])).trans t4wp
  have t7w1 := (t7l (ofString "w1") (by simp [wn])).trans t4w1
  have t7w2 := (t7l (ofString "w2") (by simp [wn])).trans t4w2
  rw [source_stateless_middle_witness] at r7
  have args7 : evalListHOLFinite t7 (h := fun address => Classical.propDecidable (t7.memaddrs address))
      statelessMiddleWitnessArguments = some [.val (.word (WP + A1)), .val (.word (A2 - A1)),
        .val (.word 9223372036854775807), .val (.word 65536)] := by
    simp [statelessMiddleWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact,
      t7wp, t7w1, t7w2, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t8, o8, a8, c8, k8, n8, cd8, m8, ⟨H2, hh2, g2H, b2, al2, oth2⟩, r8, g8, mm8⟩ :=
    ret_bytesListDecl_mem t7 o5 (ofString "cd") _ _ _ _ _ _ H1 w v t7c args7 (by rw [g7, gu1]; exact hh1) b1 al1
      (by omega) r7
  have t8si : t8.locals.lookup (ofString "si") = some (.val (.word S)) :=
    (k8 _ (by simp [wn])).trans ((t7l _ (by simp [wn])).trans t4si)
  rw [source_stateless_witness_store43] at r8
  obtain ⟨u2, mu2, lu2, gu2, cu2, ru2⟩ := ret_siStore_mem t8 o8 56 0 "cd" _ S a8 c8 w v (Or.inl rfl) t8si n8 s56 r8
  rw [source_stateless_witness_store44] at ru2
  obtain ⟨t10, m10, l10, g10, c10, r10⟩ := ret_siStore_mem u2 o8 64 1 "cd" _ S a8 c8 w v (Or.inr rfl)
    (by rw [lu2]; exact t8si) (by rw [lu2]; exact n8) s64 ru2
  have t10l : ∀ k, k ≠ ofString "st0" → k ≠ ofString "cd" → t10.locals.lookup k = t4.locals.lookup k := by
    intro k a b; rw [l10, lu2]; exact (k8 k b).trans (t7l k a)
  have t10c : t10.code = originalRuntimeCode := by rw [c10, cu2]; exact cd8.trans t7c
  have t10wp := (t10l (ofString "wp") (by simp [wn]) (by simp [wn])).trans t4wp
  have t10wl := (t10l (ofString "wlen") (by simp [wn]) (by simp [wn])).trans t4wl
  have t10w2 := (t10l (ofString "w2") (by simp [wn]) (by simp [wn])).trans t4w2
  rw [source_stateless_last_witness] at r10
  have args10 : evalListHOLFinite t10 (h := fun address => Classical.propDecidable (t10.memaddrs address))
      statelessLastWitnessArguments = some [.val (.word (WP + A2)), .val (.word (WL - A2)),
        .val (.word 256), .val (.word 1024)] := by
    simp [statelessLastWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact,
      t10wp, t10wl, t10w2, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t11, o11, a11, c11, k11, n11, _, m11, _, r11, _, mm11⟩ :=
    ret_bytesListDecl_mem t10 o8 (ofString "hd") _ _ _ _ _ _ H2 w v t10c args10 (by rw [g10, gu2]; exact hh2) b2 al2
      (by omega) r10
  have t11si : t11.locals.lookup (ofString "si") = some (.val (.word S)) :=
    (k11 _ (by simp [wn])).trans ((t10l _ (by simp [wn]) (by simp [wn])).trans t4si)
  rw [source_stateless_witness_store46] at r11
  obtain ⟨u3, mu3, lu3, _, _, ru3⟩ := ret_siStore_mem t11 o11 72 0 "hd" _ S a11 c11 w v (Or.inl rfl) t11si n11 s72 r11
  rw [source_stateless_witness_store47] at ru3
  obtain ⟨t13, m13, l13, _, _, r13⟩ := ret_siStore_mem u3 o11 80 1 "hd" _ S a11 c11 w v (Or.inr rfl)
    (by rw [lu3]; exact t11si) (by rw [lu3]; exact n11) s80 ru3
  have t13si : t13.locals.lookup (ofString "si") = some (.val (.word S)) := by rw [l13, lu3]; exact t11si
  rw [source_stateless_witness_return, evaluateHOLFiniteState_return] at r13
  simp only [evalHOLExact, lookupKvarHOLExact, t13si] at r13
  simp [shapeOfHOLExact] at r13
  obtain ⟨_, rfl⟩ := r13
  have om : out.memory = o3.memory := by
    rw [e2]; show o1.memory = _; rw [e3]; show o2.memory = _; rw [e4]
  rw [om, mm5, mm8, mm11]
  show t13.memory w = _
  rw [m13, mu3, m11, m10, mu2, m8, m7, mu1, m5, t4m]

#print axioms witness35_memory

/-- Every returned run of the actual witness suffix At32..At48 keeps every
memory word below the entry heap except the three scratch offset cells and
the six si witness header cells. -/
theorem stateless_witness_returned_memory {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (WP WL S offsets H w : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hwp : s.locals.lookup (ofString "wp") = some (.val (.word WP)))
    (hwl : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (hsi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (heapBound : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0) (below : w.toNat < H.toNat)
    (scratch : w ≠ offsets ∧ w ≠ offsets + 8 ∧ w ≠ offsets + 16)
    (headers : w ≠ S + 40 ∧ w ≠ S + 48 ∧ w ≠ S + 56 ∧ w ≠ S + 64 ∧ w ≠ S + 72 ∧ w ≠ S + 80)
    (run : evaluateHOLFiniteState s (statelessAt 32) = (some (.returned v), post)) :
    post.memory w = s.memory w := by
  rcases evaluate_stateless_witness_setup s WL offsets code hwl hg with ⟨E, W0, W1, W2, entry, eq⟩ | ⟨x, h1, h2, _⟩
  · rw [eq] at run
    obtain ⟨_, _, others, eg, _, ec, _, _, _, _, _, _, _, _, em⟩ := entry
    cases hE : evaluateHOLFiniteState E (statelessAt 35) with
    | mk r o =>
      rw [hE] at run
      obtain ⟨r1, r2⟩ := Prod.mk.inj run
      dsimp only at r1 r2
      subst r1
      have iwp : ofString "wp" ≠ ofString "i" := by decide_cbv
      have iwl : ofString "wlen" ≠ ofString "i" := by decide_cbv
      have isi : ofString "si" ≠ ofString "i" := by decide_cbv
      have frame := witness35_memory E o WP WL S offsets H w v (by rw [ec]; exact code)
        ⟨(others _ iwp).trans hwp, (others _ iwl).trans hwl, (others _ isi).trans hsi⟩
        (by rw [eg]; exact hg) (by rw [eg]; exact heap) heapBound aligned below headers hE
      rw [← r2]
      show o.memory w = _
      rw [frame, em]
      simp only [wmem, if_neg scratch.2.2, if_neg scratch.2.1, if_neg scratch.1]
  · rw [run] at h1
    exact absurd (Option.some.inj h1).symm (h2 v)

#print axioms stateless_witness_returned_memory
end InitECandidate.Runtime