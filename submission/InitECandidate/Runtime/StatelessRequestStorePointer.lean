import InitECandidate.Runtime.StatelessRequestStoreEntries
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned store/witness suffix leaves the request-table pointer readable
in its actual stateless-input header cell. -/
theorem stateless_request_store_pointer {F : Type} (t1 o1 : PanSemStateFiniteExact 64 F)
    (P L OW S offsets H1 record : BitVec 64) (v : ValueHOL 64)
    (code : t1.code = originalRuntimeCode)
    (t1si : t1.locals.lookup (ofString "si") = some (.val (.word S)))
    (t1p : t1.locals.lookup (ofString "p") = some (.val (.word P)))
    (t1len : t1.locals.lookup (ofString "len") = some (.val (.word L)))
    (t1ow : t1.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (rq1 : t1.locals.lookup (ofString "rq") = some (.val (.word record)))
    (hg : t1.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hh1 : t1.globals.lookup (ofString "heap_ptr") = some (.val (.word H1)))
    (b1 : H1.toNat ≤ 33806089496) (a1 : H1.toNat % 8 = 0)
    (headerBefore : S.toNat + 88 ≤ H1.toNat) (scratchBefore : offsets.toNat + 24 ≤ S.toNat)
    (r1 : evaluateHOLFiniteState t1 (statelessAt 29) = (some (.returned v),o1)) :
    o1.memaddrs (S + (32#64)) ∧ o1.memory (S + (32#64)) = .word record := by
  have finalMetadata := evaluateHOLFiniteState_metadata t1 (statelessAt 29)
  rw [r1] at finalMetadata
  -- si+32 store
  rw [source_stateless_request_store, evaluateHOLFiniteState_seq_line780] at r1
  unfold statelessRequestStore at r1
  have addr : @evalHOLExact 64 F _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
      (.op .add [.var .local (ofString "si"), .const 32]) = some (.val (.word (S + (32#64)))) := by
    simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]
  have frame2 := fun (w : BitVec 64) (hw : w ≠ S + (32#64)) => evaluate_wordStore_memory_frame t1 _
    (.var .local (ofString "rq")) (S + (32#64)) w addr (fun parsed h => by simp [evalHOLExact, rq1] at h; exact ⟨_, h.symm⟩) hw
  rcases evaluate_store_cases t1 (.op .add [.var .local (ofString "si"), .const 32]) (.var .local (ofString "rq"))
    with err | ⟨M, ok⟩
  · rw [err] at r1; simp at r1
  have stored := ok
  rw [evaluateHOLFiniteState_store,addr] at stored
  have valueEval : @evalHOLExact 64 F _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
      (.var .local (ofString "rq")) = some (.val (.word record)) := by simp [evalHOLExact,rq1]
  rw [valueEval] at stored
  have accessible : t1.memaddrs (S + (32#64)) := by
    by_contra inaccessible
    simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,inaccessible] at stored
  have storedCell : M (S + (32#64)) = .word record := by
    simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible] at stored
    rw [← stored]
    simp [FUPDATE]
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
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact t2c.trans (code)
  have t4m : ∀ w, t4.memory w = t2.memory w := by intro w; rw [← ht4]; rfl
  have hhs : ofString "heap_ptr" ≠ ofString "ssz_offs" := by decide_cbv
  have t4off : t4.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
    rw [t4g]; exact hg
  have t4heap : t4.globals.lookup (ofString "heap_ptr") = some (.val (.word H1)) := by rw [t4g]; exact hh1
  have addressNat : (S + (32#64)).toNat = S.toNat + 32 := by
    change (S + (32#64)).toNat = _
    exact word_add_toNat S 32 (by omega)
  have separate (base : BitVec 64) (offset : Nat) (bound : base.toNat + offset < 2^64)
      (different : S.toNat + 32 ≠ base.toNat + offset) : S + (32#64) ≠ base + BitVec.ofNat 64 offset := by
    apply word_ne_of_toNat
    rw [addressNat,word_add_toNat base offset bound]
    exact different
  have retained := stateless_witness_returned_memory t4 o4 (P + OW) (L - OW) S offsets H1 (S + (32#64)) v
    t4c t4wp t4wl t4si t4off t4heap b1 a1 (by rw [addressNat]; omega)
    ⟨by simpa using separate offsets 0 (by omega) (by omega),
      separate offsets 8 (by omega) (by omega),separate offsets 16 (by omega) (by omega)⟩
    ⟨separate S 40 (by omega) (by omega),separate S 48 (by omega) (by omega),
      separate S 56 (by omega) (by omega),separate S 64 (by omega) (by omega),
      separate S 72 (by omega) (by omega),separate S 80 (by omega) (by omega)⟩ r4
  refine ⟨?_,?_⟩
  · rw [finalMetadata.2.1]; exact accessible
  · rw [e3]
    show o3.memory (S + (32#64)) = _
    rw [e4]
    change o4.memory (S + (32#64)) = _
    rw [retained,t4m,← ht2]
    exact storedCell

#print axioms stateless_request_store_pointer
end InitECandidate.Runtime
