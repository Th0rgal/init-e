import InitECandidate.Runtime.BytesListDeclarationHeapUpper
import InitECandidate.Runtime.StatelessCheckedOffsetCall
import InitECandidate.Runtime.StatelessWitnessOffsetBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness35_heap_upper {F : Type} (E out : PanSemStateFiniteExact 64 F) (WP WL S offsets Hc : BitVec 64)
    (v : ValueHOL 64) (code : E.code = originalRuntimeCode) (loc : WLocals E WP WL S)
    (hg : E.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : E.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc)))
    (hb : Hc.toNat ≤ 33806089496) (ha : Hc.toNat % 8 = 0)
    (run : evaluateHOLFiniteState E (statelessAt 35) = (some (.returned v), out)) :
    ∃ Hf : BitVec 64, out.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ Hc.toNat ≤ Hf.toNat ∧Hf.toNat≤Hc.toNat+12*WL.toNat+21 := by
  have wn := witness_names
  simp only [ne_eq] at wn
  obtain ⟨hwp, hwl, hsi⟩ := loc
  rw [source_stateless_witness_check] at run
  obtain ⟨t1, r1, l1, g1, c1, mem1, dom1, checked⟩ := ret_checkCall_checked E out _ offsets WL v code hg hwl run
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
  have t1off : t1.globals.lookup (ofString "ssz_offs")=some (.val (.word offsets)) := by rw [g1];exact hg
  have read0:=eval_load_word_mem_at t1 _ offsets A0 (by simp [evalHOLExact,t1off]) init0
  have read1:=eval_load_word_mem_at (setVarHOLFinite (ofString "w0") (.val (.word A0)) t1) _ (offsets+8) A1
    (by simp [evalHOLExact,evalListHOLExact,setVarHOLFinite,t1off,wordOpHOL,wordOp,valueIsWord,valueWord]) init1
  have read2:=eval_load_word_mem_at (setVarHOLFinite (ofString "w1") (.val (.word A1)) (setVarHOLFinite (ofString "w0") (.val (.word A0)) t1)) _ (offsets+16) A2
    (by simp [evalHOLExact,evalListHOLExact,setVarHOLFinite,t1off,wordOpHOL,wordOp,valueIsWord,valueWord]) init2
  change memWord t1.memory (offsets+8)=A1 at read1
  change memWord t1.memory (offsets+16)=A2 at read2
  obtain ⟨firstEq,middleLower,middleLast,lastUpper⟩:=stateless_witness_offset_bounds t1 offsets WL A0 A1 A2 ((checked.2.2 (by decide)).2) checked.2.1 read0 read1 read2
  have firstMiddle : A0.toNat≤A1.toNat := by rw [firstEq];exact middleLower
  have firstLength : (A1-A0).toNat≤WL.toNat := by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr firstMiddle)];omega
  have middleLength : (A2-A1).toNat≤WL.toNat := by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr middleLast)];omega
  have lastLength : (WL-A2).toNat≤WL.toNat := by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr lastUpper)];omega
  rw [source_stateless_first_witness] at r4
  have args4 : evalListHOLFinite t4 (h := fun address => Classical.propDecidable (t4.memaddrs address))
      statelessFirstWitnessArguments = some [.val (.word (WP + A0)), .val (.word (A1 - A0)),
        .val (.word 9223372036854775807), .val (.word 1024)] := by
    simp [statelessFirstWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, t4wp, t4w0, t4w1,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t5, o5, _, _, k5, _, cd5, ⟨H1, hh1, g1H, b1, al1, upper1, _⟩, r5, g5, _⟩ :=
    ret_bytesListDecl_heap_upper t4 o3 (ofString "st0") _ _ _ _ _ _ Hc v t4c args4 (by rw [t4g]; exact heap) hb ha r4
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
  obtain ⟨t8, o8, _, _, k8, _, cd8, ⟨H2, hh2, g2H, b2, al2, upper2, _⟩, r8, g8, _⟩ :=
    ret_bytesListDecl_heap_upper t7 o5 (ofString "cd") _ _ _ _ _ _ H1 v t7c args7 (by rw [t7g]; exact hh1) b1 al1 r7
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
  obtain ⟨t11, o11, _, _, k11, _, _, ⟨H3, hh3, g3H, _, _, upper3, _⟩, r11, g11, _⟩ :=
    ret_bytesListDecl_heap_upper t10 o8 (ofString "hd") _ _ _ _ _ _ H2 v t10c args10 (by rw [t10g]; exact hh2) b2 al2 r10
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
  exact ⟨H3, by rw [og, t13g]; exact hh3, by omega,by omega⟩

#print axioms witness35_heap_upper

theorem stateless_witness_heap_upper {F : Type} (s post : PanSemStateFiniteExact 64 F) (WP WL S offsets H : BitVec 64)
    (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hwp : s.locals.lookup (ofString "wp") = some (.val (.word WP)))
    (hwl : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (hsi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (heapBound : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (run : evaluateHOLFiniteState s (statelessAt 32) = (some (.returned v), post)) :
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat ≤ Hf.toNat ∧Hf.toNat≤H.toNat+12*WL.toNat+21 := by
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
      obtain ⟨Hf, h1, h2⟩ := witness35_heap_upper E o WP WL S offsets H v (by rw [ec]; exact code)
        ⟨(others _ iwp).trans hwp, (others _ iwl).trans hwl, (others _ isi).trans hsi⟩
        (by rw [eg]; exact hg) (by rw [eg]; exact heap) heapBound aligned hE
      exact ⟨Hf, by rw [← r2]; exact h1, h2⟩
  · rw [run] at h1
    exact absurd (Option.some.inj h1).symm (h2 v)


#print axioms stateless_witness_heap_upper
end InitECandidate.Runtime
