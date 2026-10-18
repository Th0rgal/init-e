import InitECandidate.Runtime.StatelessWitnessDeclReturned
import InitECandidate.Runtime.StatelessWitnessSetupRun
import InitECandidate.Runtime.StatelessWitnessLoadsBound
import InitECandidate.Runtime.StatelessWitnessListsBound
import InitECandidate.Runtime.StatelessWitnessMiddleBound
import InitECandidate.Runtime.StatelessWitnessLastBound
import InitECandidate.Runtime.LoadOneWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_stateless_witness_store40 : statelessAt 40 =
    .seq (.store (.op .add [.var .local (ofString "si"), .const 40]) (.rfield 0 (.var .local (ofString "st0"))))
      (statelessAt 41) := by
  simp only [statelessAt, statelessNext, sourceFunctionBody, InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_store41 : statelessAt 41 =
    .seq (.store (.op .add [.var .local (ofString "si"), .const 48]) (.rfield 1 (.var .local (ofString "st0"))))
      (statelessAt 42) := by
  simp only [statelessAt, statelessNext, sourceFunctionBody, InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_store43 : statelessAt 43 =
    .seq (.store (.op .add [.var .local (ofString "si"), .const 56]) (.rfield 0 (.var .local (ofString "cd"))))
      (statelessAt 44) := by
  simp only [statelessAt, statelessNext, sourceFunctionBody, InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_store44 : statelessAt 44 =
    .seq (.store (.op .add [.var .local (ofString "si"), .const 64]) (.rfield 1 (.var .local (ofString "cd"))))
      (statelessAt 45) := by
  simp only [statelessAt, statelessNext, sourceFunctionBody, InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_store46 : statelessAt 46 =
    .seq (.store (.op .add [.var .local (ofString "si"), .const 72]) (.rfield 0 (.var .local (ofString "hd"))))
      (statelessAt 47) := by
  simp only [statelessAt, statelessNext, sourceFunctionBody, InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_store47 : statelessAt 47 =
    .seq (.store (.op .add [.var .local (ofString "si"), .const 80]) (.rfield 1 (.var .local (ofString "hd"))))
      (statelessAt 48) := by
  simp only [statelessAt, statelessNext, sourceFunctionBody, InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_return : statelessAt 48 = .return (.var .local (ofString "si")) := by
  simp only [statelessAt, statelessNext, sourceFunctionBody, InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Locals the witness suffix reads, all words. -/
def WLocals {F : Type} (t : PanSemStateFiniteExact 64 F) (WP WL S : BitVec 64) : Prop :=
  t.locals.lookup (ofString "wp") = some (.val (.word WP)) ∧
  t.locals.lookup (ofString "wlen") = some (.val (.word WL)) ∧
  t.locals.lookup (ofString "si") = some (.val (.word S))

theorem wlocals_keep {F : Type} (t t' : PanSemStateFiniteExact 64 F) (WP WL S : BitVec 64) (name : MlS)
    (n1 : ofString "wp" ≠ name) (n2 : ofString "wlen" ≠ name) (n3 : ofString "si" ≠ name)
    (keep : ∀ k, k ≠ name → t'.locals.lookup k = t.locals.lookup k) (h : WLocals t WP WL S) : WLocals t' WP WL S :=
  ⟨(keep _ n1).trans h.1, (keep _ n2).trans h.2.1, (keep _ n3).trans h.2.2⟩

theorem witness_names :
    ofString "wp" ≠ ofString "wlen" ∧
    ofString "wp" ≠ ofString "si" ∧
    ofString "wp" ≠ ofString "w0" ∧
    ofString "wp" ≠ ofString "w1" ∧
    ofString "wp" ≠ ofString "w2" ∧
    ofString "wp" ≠ ofString "st0" ∧
    ofString "wp" ≠ ofString "cd" ∧
    ofString "wp" ≠ ofString "hd" ∧
    ofString "wlen" ≠ ofString "wp" ∧
    ofString "wlen" ≠ ofString "si" ∧
    ofString "wlen" ≠ ofString "w0" ∧
    ofString "wlen" ≠ ofString "w1" ∧
    ofString "wlen" ≠ ofString "w2" ∧
    ofString "wlen" ≠ ofString "st0" ∧
    ofString "wlen" ≠ ofString "cd" ∧
    ofString "wlen" ≠ ofString "hd" ∧
    ofString "si" ≠ ofString "wp" ∧
    ofString "si" ≠ ofString "wlen" ∧
    ofString "si" ≠ ofString "w0" ∧
    ofString "si" ≠ ofString "w1" ∧
    ofString "si" ≠ ofString "w2" ∧
    ofString "si" ≠ ofString "st0" ∧
    ofString "si" ≠ ofString "cd" ∧
    ofString "si" ≠ ofString "hd" ∧
    ofString "w0" ≠ ofString "wp" ∧
    ofString "w0" ≠ ofString "wlen" ∧
    ofString "w0" ≠ ofString "si" ∧
    ofString "w0" ≠ ofString "w1" ∧
    ofString "w0" ≠ ofString "w2" ∧
    ofString "w0" ≠ ofString "st0" ∧
    ofString "w0" ≠ ofString "cd" ∧
    ofString "w0" ≠ ofString "hd" ∧
    ofString "w1" ≠ ofString "wp" ∧
    ofString "w1" ≠ ofString "wlen" ∧
    ofString "w1" ≠ ofString "si" ∧
    ofString "w1" ≠ ofString "w0" ∧
    ofString "w1" ≠ ofString "w2" ∧
    ofString "w1" ≠ ofString "st0" ∧
    ofString "w1" ≠ ofString "cd" ∧
    ofString "w1" ≠ ofString "hd" ∧
    ofString "w2" ≠ ofString "wp" ∧
    ofString "w2" ≠ ofString "wlen" ∧
    ofString "w2" ≠ ofString "si" ∧
    ofString "w2" ≠ ofString "w0" ∧
    ofString "w2" ≠ ofString "w1" ∧
    ofString "w2" ≠ ofString "st0" ∧
    ofString "w2" ≠ ofString "cd" ∧
    ofString "w2" ≠ ofString "hd" ∧
    ofString "st0" ≠ ofString "wp" ∧
    ofString "st0" ≠ ofString "wlen" ∧
    ofString "st0" ≠ ofString "si" ∧
    ofString "st0" ≠ ofString "w0" ∧
    ofString "st0" ≠ ofString "w1" ∧
    ofString "st0" ≠ ofString "w2" ∧
    ofString "st0" ≠ ofString "cd" ∧
    ofString "st0" ≠ ofString "hd" ∧
    ofString "cd" ≠ ofString "wp" ∧
    ofString "cd" ≠ ofString "wlen" ∧
    ofString "cd" ≠ ofString "si" ∧
    ofString "cd" ≠ ofString "w0" ∧
    ofString "cd" ≠ ofString "w1" ∧
    ofString "cd" ≠ ofString "w2" ∧
    ofString "cd" ≠ ofString "st0" ∧
    ofString "cd" ≠ ofString "hd" ∧
    ofString "hd" ≠ ofString "wp" ∧
    ofString "hd" ≠ ofString "wlen" ∧
    ofString "hd" ≠ ofString "si" ∧
    ofString "hd" ≠ ofString "w0" ∧
    ofString "hd" ≠ ofString "w1" ∧
    ofString "hd" ≠ ofString "w2" ∧
    ofString "hd" ≠ ofString "st0" ∧
    ofString "hd" ≠ ofString "cd" := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide_cbv

/-- Every returned run of the actual witness suffix At35..At48 returns si and
keeps a capped aligned heap and all non-allocator globals. -/
theorem witness35_returned {F : Type} (s0 E out : PanSemStateFiniteExact 64 F) (WP WL S offsets : BitVec 64)
    (v : ValueHOL 64) (code : E.code = originalRuntimeCode) (loc : WLocals E WP WL S)
    (hg : E.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))) (frame : HeapFrame s0 E)
    (run : evaluateHOLFiniteState E (statelessAt 35) = (some (.returned v), out)) :
    v = .val (.word S) ∧ HeapFrame s0 out := by
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
  have t4si := (t4l _ (by simp [wn]) (by simp [wn]) (by simp [wn])).trans hsi
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact c1.trans code
  have t4g : t4.globals = E.globals := by rw [← ht4]; exact g1
  have frame4 : HeapFrame s0 t4 := by unfold HeapFrame; rw [t4g]; exact frame
  -- first list
  rw [source_stateless_first_witness] at r4
  have args4 : evalListHOLFinite t4 (h := fun address => Classical.propDecidable (t4.memaddrs address))
      statelessFirstWitnessArguments = some [.val (.word (WP + A0)), .val (.word (A1 - A0)),
        .val (.word 9223372036854775807), .val (.word 1024)] := by
    simp [statelessFirstWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, t4wp, t4w0, t4w1,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t5, o5, k5, c5, frame5, r5, g5⟩ := ret_bytesListDecl s0 t4 o3 (ofString "st0") _ _ _ _ _ _ v t4c args4 frame4 r4
  rw [source_stateless_witness_store40] at r5
  obtain ⟨M5, r6⟩ := ret_storeSeq _ _ _ _ _ v r5
  rw [source_stateless_witness_store41] at r6
  obtain ⟨M6, r7⟩ := ret_storeSeq _ _ _ _ _ v r6
  generalize ht7 : ({({t5 with memory := M5} : PanSemStateFiniteExact 64 F) with memory := M6} :
    PanSemStateFiniteExact 64 F) = t7 at r7
  have t7l : ∀ k, k ≠ ofString "st0" → t7.locals.lookup k = t4.locals.lookup k := by
    intro k hk; rw [← ht7]; exact k5 k hk
  have t7c : t7.code = originalRuntimeCode := by rw [← ht7]; exact c5.trans t4c
  have frame7 : HeapFrame s0 t7 := by rw [← ht7]; exact frame5
  -- middle list
  have t7wp := (t7l (ofString "wp") (by simp [wn])).trans t4wp
  have t7w1 := (t7l (ofString "w1") (by simp [wn])).trans t4w1
  have t7w2 := (t7l (ofString "w2") (by simp [wn])).trans t4w2
  rw [source_stateless_middle_witness] at r7
  have args7 : evalListHOLFinite t7 (h := fun address => Classical.propDecidable (t7.memaddrs address))
      statelessMiddleWitnessArguments = some [.val (.word (WP + A1)), .val (.word (A2 - A1)),
        .val (.word 9223372036854775807), .val (.word 65536)] := by
    simp [statelessMiddleWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact,
      t7wp, t7w1, t7w2, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t8, o8, k8, c8, frame8, r8, g8⟩ := ret_bytesListDecl s0 t7 _ (ofString "cd") _ _ _ _ _ _ v t7c args7 frame7 r7
  rw [source_stateless_witness_store43] at r8
  obtain ⟨M8, r9⟩ := ret_storeSeq _ _ _ _ _ v r8
  rw [source_stateless_witness_store44] at r9
  obtain ⟨M9, r10⟩ := ret_storeSeq _ _ _ _ _ v r9
  generalize ht10 : ({({t8 with memory := M8} : PanSemStateFiniteExact 64 F) with memory := M9} :
    PanSemStateFiniteExact 64 F) = t10 at r10
  have t10l : ∀ k, k ≠ ofString "st0" → k ≠ ofString "cd" → t10.locals.lookup k = t4.locals.lookup k := by
    intro k a b; rw [← ht10]; exact (k8 k b).trans (t7l k a)
  have t10c : t10.code = originalRuntimeCode := by rw [← ht10]; exact c8.trans t7c
  have frame10 : HeapFrame s0 t10 := by rw [← ht10]; exact frame8
  -- last list
  have t10wp := (t10l (ofString "wp") (by simp [wn]) (by simp [wn])).trans t4wp
  have t10wl := (t10l (ofString "wlen") (by simp [wn]) (by simp [wn])).trans t4wl
  have t10w2 := (t10l (ofString "w2") (by simp [wn]) (by simp [wn])).trans t4w2
  rw [source_stateless_last_witness] at r10
  have args10 : evalListHOLFinite t10 (h := fun address => Classical.propDecidable (t10.memaddrs address))
      statelessLastWitnessArguments = some [.val (.word (WP + A2)), .val (.word (WL - A2)),
        .val (.word 256), .val (.word 1024)] := by
    simp [statelessLastWitnessArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact,
      t10wp, t10wl, t10w2, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t11, o11, k11, _, frame11, r11, g11⟩ := ret_bytesListDecl s0 t10 _ (ofString "hd") _ _ _ _ _ _ v t10c args10
    frame10 r10
  rw [source_stateless_witness_store46] at r11
  obtain ⟨M11, r12⟩ := ret_storeSeq _ _ _ _ _ v r11
  rw [source_stateless_witness_store47] at r12
  obtain ⟨M12, r13⟩ := ret_storeSeq _ _ _ _ _ v r12
  generalize ht13 : ({({t11 with memory := M11} : PanSemStateFiniteExact 64 F) with memory := M12} :
    PanSemStateFiniteExact 64 F) = t13 at r13
  have t13si : t13.locals.lookup (ofString "si") = some (.val (.word S)) := by
    rw [← ht13]; exact (k11 (ofString "si") (by simp [wn])).trans ((t10l (ofString "si") (by simp [wn]) (by simp [wn])).trans t4si)
  have frame13 : HeapFrame s0 t13 := by rw [← ht13]; exact frame11
  rw [source_stateless_witness_return, evaluateHOLFiniteState_return] at r13
  simp only [evalHOLExact, lookupKvarHOLExact, t13si] at r13
  simp [shapeOfHOLExact] at r13
  obtain ⟨rfl, rfl⟩ := r13
  refine ⟨rfl, ?_⟩
  have og : out.globals = t13.globals := by
    rw [e2]; show o1.globals = _; rw [e3]; show o2.globals = _; rw [e4]; show o3.globals = _
    rw [g5, g8, g11]; rfl
  unfold HeapFrame; rw [og]; exact frame13

/-- Every returned run of the actual original witness suffix At32..At48 returns
the word in local si; the heap stays capped and aligned (given an aligned
capped entry heap) and every non-allocator global equals its entry value. -/
theorem stateless_witness_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (WP WL S offsets H : BitVec 64)
    (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hwp : s.locals.lookup (ofString "wp") = some (.val (.word WP)))
    (hwl : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (hsi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (heapBound : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (run : evaluateHOLFiniteState s (statelessAt 32) = (some (.returned v), post)) :
    v = .val (.word S) ∧ HeapFrame s post := by
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
      obtain ⟨hv, frame⟩ := witness35_returned s E o WP WL S offsets v (by rw [ec]; exact code)
        ⟨(others _ iwp).trans hwp, (others _ iwl).trans hwl, (others _ isi).trans hsi⟩
        (by rw [eg]; exact hg) ⟨⟨H, by rw [eg]; exact heap, heapBound, aligned⟩, fun k _ => by rw [eg]⟩ hE
      refine ⟨hv, ?_⟩
      unfold HeapFrame at frame ⊢
      rw [← r2]; exact frame
  · rw [run] at h1
    exact absurd (Option.some.inj h1).symm (h2 v)

#print axioms witness35_returned
#print axioms stateless_witness_returned
end InitECandidate.Runtime
