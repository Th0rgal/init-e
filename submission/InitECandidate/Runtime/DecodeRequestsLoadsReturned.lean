import InitECandidate.Runtime.DecodeRequestsCountsReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem reqLoadDec_returned {σ : Type} (s post : PanSemStateFiniteExact 64 σ) (name : String) (a : ExpHOL 64)
    (body : ProgHOL 64) (A : BitVec 64) (v : ValueHOL 64)
    (ha : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a = some (.val (.word A)))
    (run : evaluateHOLFiniteState s (.dec (ofString name) .one (.load .one a) body) = (some (.returned v), post)) :
    s.memaddrs A ∧ ∃ out, evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (memWord s.memory A))) s) body =
      (some (.returned v), out) ∧ post.memory = out.memory ∧ post.globals = out.globals ∧ post.memaddrs = out.memaddrs := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  by_cases dom : s.memaddrs A
  · have load : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.load .one a) =
        some (.val (.word (memWord s.memory A))) := by
      rw [evalHOLExact]
      simp [ha, memLoadHOLExact, isWfShapeExactHOL, dom, memWord]
    simp only [load, shapeOfHOLExact, shapeEqHOL, if_true] at run
    cases inner : evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (memWord s.memory A))) s) body with
    | mk r out =>
      rw [inner] at run
      obtain ⟨r1, r2⟩ := Prod.mk.inj run
      dsimp only at r1 r2
      subst r1
      refine ⟨dom, out, rfl, ?_, ?_, ?_⟩ <;> rw [← r2]
  · have load : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.load .one a) = none := by
      rw [evalHOLExact]
      simp [ha, memLoadHOLExact, isWfShapeExactHOL, dom]
    simp only [load] at run
    simp at run

#print axioms reqLoadDec_returned

theorem reqLoad_names : ofString "o0" ≠ ofString "o1" ∧ ofString "o0" ≠ ofString "o2" ∧ ofString "o0" ≠ ofString "o3" ∧
    ofString "o0" ≠ ofString "o4" ∧ ofString "o1" ≠ ofString "o2" ∧ ofString "o1" ≠ ofString "o3" ∧
    ofString "o1" ≠ ofString "o4" ∧ ofString "o2" ≠ ofString "o3" ∧ ofString "o2" ≠ ofString "o4" ∧
    ofString "o3" ≠ ofString "o4" ∧ ofString "rq" ≠ ofString "o0" ∧ ofString "rq" ≠ ofString "o1" ∧
    ofString "rq" ≠ ofString "o2" ∧ ofString "rq" ≠ ofString "o3" ∧ ofString "rq" ≠ ofString "o4" ∧
    ofString "p" ≠ ofString "o0" ∧ ofString "p" ≠ ofString "o1" ∧ ofString "p" ≠ ofString "o2" ∧
    ofString "p" ≠ ofString "o3" ∧ ofString "p" ≠ ofString "o4" ∧ ofString "len" ≠ ofString "o0" ∧
    ofString "len" ≠ ofString "o1" ∧ ofString "len" ≠ ofString "o2" ∧ ofString "len" ≠ ofString "o3" ∧
    ofString "len" ≠ ofString "o4" := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide_cbv

theorem reqLoad_names' : ofString "o0" ≠ ofString "rq" ∧ ofString "o1" ≠ ofString "rq" ∧ ofString "o2" ≠ ofString "rq" ∧ ofString "o3" ≠ ofString "rq" ∧ ofString "o4" ≠ ofString "rq" ∧ ofString "o0" ≠ ofString "p" ∧ ofString "o1" ≠ ofString "p" ∧ ofString "o2" ≠ ofString "p" ∧ ofString "o3" ≠ ofString "p" ∧ ofString "o4" ≠ ofString "p" ∧ ofString "o0" ≠ ofString "len" ∧ ofString "o1" ≠ ofString "len" ∧ ofString "o2" ≠ ofString "len" ∧ ofString "o3" ≠ ofString "len" ∧ ofString "o4" ≠ ofString "len" ∧ ofString "o1" ≠ ofString "o0" ∧ ofString "o2" ≠ ofString "o0" ∧ ofString "o3" ≠ ofString "o0" ∧ ofString "o4" ≠ ofString "o0" ∧ ofString "o2" ≠ ofString "o1" ∧ ofString "o3" ≠ ofString "o1" ∧ ofString "o4" ≠ ofString "o1" ∧ ofString "o3" ≠ ofString "o2" ∧ ofString "o4" ≠ ofString "o2" ∧ ofString "o4" ≠ ofString "o3" := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide_cbv

/-- A returned run of the five offset loads: the five scratch cells are
readable, o_k is the word at ssz_offs+8k, and the count/store facts follow. -/
theorem reqLoads_returned {σ : Type} (s post : PanSemStateFiniteExact 64 σ) (rq p L offsets : BitVec 64)
    (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (hrq : s.locals.lookup (ofString "rq") = some (.val (.word rq)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (run : evaluateHOLFiniteState s reqLoads = (some (.returned v), post)) :
    let O0 := memWord s.memory offsets
    let O1 := memWord s.memory (offsets + 8)
    let O2 := memWord s.memory (offsets + 16)
    let O3 := memWord s.memory (offsets + 24)
    let O4 := memWord s.memory (offsets + 32)
    s.memaddrs offsets ∧ s.memaddrs (offsets + 8) ∧ s.memaddrs (offsets + 16) ∧ s.memaddrs (offsets + 24) ∧
    s.memaddrs (offsets + 32) ∧
    (O1 - O0) % 192 = 0 ∧ (O2 - O1) % 76 = 0 ∧ (O3 - O2) % 116 = 0 ∧ (O4 - O3) % 184 = 0 ∧ (L - O4) % 68 = 0 ∧
      v = .val (.word rq) ∧
      (∀ x ∈ reqCellValues p O0 O1 O2 O3 O4 ((O1 - O0) / 192) ((O2 - O1) / 76) ((O3 - O2) / 116)
        ((O4 - O3) / 184) ((L - O4) / 68), s.memaddrs (rq + x.1)) ∧
      post.memory = memWrites s.memory rq (reqCellValues p O0 O1 O2 O3 O4 ((O1 - O0) / 192) ((O2 - O1) / 76)
        ((O3 - O2) / 116) ((O4 - O3) / 184) ((L - O4) / 68)) ∧
      post.globals = s.globals ∧ post.memaddrs = s.memaddrs := by
  intro O0 O1 O2 O3 O4
  have names := reqLoad_names
  have names' := reqLoad_names'
  simp only [ne_eq] at names names'
  unfold reqLoads at run
  obtain ⟨d0, out0, r0, pm0, pg0, pd0⟩ := reqLoadDec_returned s post "o0" _ _ offsets v (by simp [reqGlobal, evalHOLExact, hg]) run
  obtain ⟨d1, out1, r1, pm1, pg1, pd1⟩ := reqLoadDec_returned (setVarHOLFinite (ofString "o0") (.val (.word (memWord s.memory offsets))) s) out0 "o1" _ _ (offsets + 8) v (by simp [reqGlobal, setVarHOLFinite, evalHOLExact, evalListHOLExact, hg, wordOpHOL, wordOp, valueIsWord, valueWord]) r0
  obtain ⟨d2, out2, r2, pm2, pg2, pd2⟩ := reqLoadDec_returned (setVarHOLFinite (ofString "o1") (.val (.word (memWord s.memory (offsets + 8)))) (setVarHOLFinite (ofString "o0") (.val (.word (memWord s.memory offsets))) s)) out1 "o2" _ _ (offsets + 16) v (by simp [reqGlobal, setVarHOLFinite, evalHOLExact, evalListHOLExact, hg, wordOpHOL, wordOp, valueIsWord, valueWord]) r1
  obtain ⟨d3, out3, r3, pm3, pg3, pd3⟩ := reqLoadDec_returned (setVarHOLFinite (ofString "o2") (.val (.word (memWord s.memory (offsets + 16)))) (setVarHOLFinite (ofString "o1") (.val (.word (memWord s.memory (offsets + 8)))) (setVarHOLFinite (ofString "o0") (.val (.word (memWord s.memory offsets))) s))) out2 "o3" _ _ (offsets + 24) v (by simp [reqGlobal, setVarHOLFinite, evalHOLExact, evalListHOLExact, hg, wordOpHOL, wordOp, valueIsWord, valueWord]) r2
  obtain ⟨d4, out4, r4, pm4, pg4, pd4⟩ := reqLoadDec_returned (setVarHOLFinite (ofString "o3") (.val (.word (memWord s.memory (offsets + 24)))) (setVarHOLFinite (ofString "o2") (.val (.word (memWord s.memory (offsets + 16)))) (setVarHOLFinite (ofString "o1") (.val (.word (memWord s.memory (offsets + 8)))) (setVarHOLFinite (ofString "o0") (.val (.word (memWord s.memory offsets))) s)))) out3 "o4" _ _ (offsets + 32) v (by simp [reqGlobal, setVarHOLFinite, evalHOLExact, evalListHOLExact, hg, wordOpHOL, wordOp, valueIsWord, valueWord]) r3
  replace r4 : evaluateHOLFiniteState (setVarHOLFinite (ofString "o4") (.val (.word (memWord s.memory (offsets + 32)))) (setVarHOLFinite (ofString "o3") (.val (.word (memWord s.memory (offsets + 24)))) (setVarHOLFinite (ofString "o2") (.val (.word (memWord s.memory (offsets + 16)))) (setVarHOLFinite (ofString "o1") (.val (.word (memWord s.memory (offsets + 8)))) (setVarHOLFinite (ofString "o0") (.val (.word (memWord s.memory offsets))) s))))) reqCounts = (some (.returned v), out4) := r4
  generalize ht : (setVarHOLFinite (ofString "o4") (.val (.word (memWord s.memory (offsets + 32)))) (setVarHOLFinite (ofString "o3") (.val (.word (memWord s.memory (offsets + 24)))) (setVarHOLFinite (ofString "o2") (.val (.word (memWord s.memory (offsets + 16)))) (setVarHOLFinite (ofString "o1") (.val (.word (memWord s.memory (offsets + 8)))) (setVarHOLFinite (ofString "o0") (.val (.word (memWord s.memory offsets))) s))))) = t at r4
  have tm : t.memory = s.memory := by rw [← ht]; rfl
  have tg : t.globals = s.globals := by rw [← ht]; rfl
  have td : t.memaddrs = s.memaddrs := by rw [← ht]; rfl
  have facts := reqCounts_returned t out4 rq p L (memWord s.memory offsets) (memWord s.memory (offsets + 8)) (memWord s.memory (offsets + 16)) (memWord s.memory (offsets + 24)) (memWord s.memory (offsets + 32)) v (by rw [← ht]; exact code) (by rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, names, names', hrq]) (by rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, names, names', hp]) (by rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, names, names', hL]) (by rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, names, names']) (by rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, names, names']) (by rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, names, names']) (by rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, names, names']) (by rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, names, names']) r4
  rw [tm, tg, td] at facts
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := facts
  refine ⟨d0, d1, d2, d3, d4, f1, f2, f3, f4, f5, f6, f7, ?_, ?_, ?_⟩
  · rw [pm0, pm1, pm2, pm3, pm4, f8]
  · rw [pg0, pg1, pg2, pg3, pg4, f9]
  · rw [pd0, pd1, pd2, pd3, pd4, f10]

#print axioms reqLoads_returned
end InitECandidate.Runtime
