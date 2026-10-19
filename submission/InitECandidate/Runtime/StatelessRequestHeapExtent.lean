import InitECandidate.Runtime.StatelessHeapGrowth
import InitECandidate.Runtime.StatelessRequestDeclarationExtent
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Witness decoding retains the request table's complete80-byte allocation. -/
theorem stateless_request_heap_extent {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat + 80 ≤ Hf.toNat := by
  have nrq : ∀ n : String, n ∈ ["si", "p", "len", "o_wit"] → ofString n ≠ ofString "rq" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl <;> decide_cbv
  rw [source_stateless_request_call] at run
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessRequestArguments = some [.val (.word (NP + ORQ)), .val (.word (NL - ORQ))] := by
    simp [statelessRequestArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hnp, hnlen, horq,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t1, o1, k1, rq1, c1, mem1, ⟨H1, hh1, g1, b1, a1, oth1⟩, r1, pg1, pm1⟩ :=
    ret_requestsDecl_mem_extent t post (ofString "rq") _ _ (NP + ORQ) (NL - ORQ) H offsets v code args heap hg hb run
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


#print axioms stateless_request_heap_extent
end InitECandidate.Runtime
