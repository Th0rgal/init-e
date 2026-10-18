import InitECandidate.Runtime.StatelessMidNames
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem reaches_decExact {σ : Type} (t : PanSemStateFiniteExact 64 σ) (name : MlS) (e : ExpHOL 64) (w : BitVec 64)
    (body : ProgHOL 64)
    (he : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e = some (.val (.word w))) :
    Reaches t (.dec name .one e body) (fun E => E = setVarHOLFinite name (.val (.word w)) t) 0 body :=
  reaches_dec t name e body _ (fun v hv => ⟨w, by rw [he] at hv; exact (Option.some.inj hv).symm, rfl⟩)

theorem reaches_decBounded {σ : Type} (t : PanSemStateFiniteExact 64 σ) (name : MlS) (e : ExpHOL 64) (body : ProgHOL 64)
    (b : @Bounded32 σ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e) :
    Reaches t (.dec name .one e body)
      (fun E => ∃ w : BitVec 64, w.toNat < 2 ^ 32 ∧ E = setVarHOLFinite name (.val (.word w)) t) 0 body :=
  reaches_dec t name e body _ (fun v hv => by obtain ⟨w, rfl, small⟩ := b v hv; exact ⟨w, rfl, w, small, rfl⟩)

/-- Facts at the actual At22 entry (inside the At8..At17 declaration scopes). -/
def MidEntry {σ : Type} (s : PanSemStateFiniteExact 64 σ) (P H offsets : BitVec 64) (E : PanSemStateFiniteExact 64 σ) : Prop :=
  let ONP := memWord s.memory offsets
  let OW := memWord s.memory (offsets + 8)
  s.memaddrs offsets ∧ s.memaddrs (offsets + 8) ∧ (96 : BitVec 64) ≤ (33806089496 : BitVec 64) - H ∧
  ¬ OW - ONP < 44 ∧ s.memaddrs (H + 88) ∧ s.memaddrs (offsets + 16) ∧
  ∃ X88 OPL OVH ORQ : BitVec 64, OPL.toNat < 2 ^ 32 ∧ OVH.toNat < 2 ^ 32 ∧ ORQ.toNat < 2 ^ 32 ∧
    E.memory = wmem (wmem (wmem (wmem s.memory (H + 88) X88) offsets OPL) (offsets + 8) OVH) (offsets + 16) ORQ ∧
    E.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd H 96))) s).globals ∧
    E.memaddrs = s.memaddrs ∧ E.code = s.code ∧
    E.locals.lookup (ofString "o_npr") = some (.val (.word ONP)) ∧
    E.locals.lookup (ofString "o_wit") = some (.val (.word OW)) ∧
    E.locals.lookup (ofString "si") = some (.val (.word H)) ∧
    E.locals.lookup (ofString "np") = some (.val (.word (P + ONP))) ∧
    E.locals.lookup (ofString "nlen") = some (.val (.word (OW - ONP))) ∧
    E.locals.lookup (ofString "o_pl") = some (.val (.word OPL)) ∧
    E.locals.lookup (ofString "o_vh") = some (.val (.word OVH)) ∧
    E.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)) ∧
    (∀ k, k ≠ ofString "o_npr" → k ≠ ofString "o_wit" → k ≠ ofString "si" → k ≠ ofString "np" →
      k ≠ ofString "nlen" → k ≠ ofString "o_pl" → k ≠ ofString "o_vh" → k ≠ ofString "o_rq" →
      E.locals.lookup k = s.locals.lookup k) ∧
    SszCheckOffsetsReturned E offsets 3 44 (OW - ONP) (.val (.word 0))

/-- The actual original stateless prefix At8..At21 at every clock: either it
reaches At22 within 11 ticks with MidEntry facts (scoped-equal outcome), or it
aborts without returning within 11 ticks, including the allocation rejection,
unreadable loads, unwritable cells, the nlen guard and rejected offsets. -/
theorem evaluate_stateless_mid {σ : Type} (s : PanSemStateFiniteExact 64 σ) (P H offsets : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H))) (pointerBound : H.toNat ≤ 33806089496) :
    Reaches s (statelessAt 8) (MidEntry s P H offsets) 11 (statelessAt 22) := by
  obtain ⟨a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩ := source_stateless_mid
  have nm := mid_names
  simp only [ne_eq] at nm
  have hs : ofString "heap_ptr" ≠ ofString "ssz_offs" := by decide_cbv
  refine reaches_mono s _ _ (MidEntry s P H offsets) (MidEntry s P H offsets)
    (0 + (0 + (2 + (0 + (0 + (0 + (1 + (0 + (0 + (0 + (0 + (0 + (0 + 8))))))))))))) 11 (by decide) (fun _ h => h) ?_
  rw [a8]
  refine reaches_trans s _ (statelessAt 9) _ _ _ _ _ (reaches_loadDec s _ _ offsets _
    (by simp [stOffsetsGlobal, evalHOLExact, hg])) ?_
  rintro _ ⟨d0, rfl⟩
  rw [a9]
  refine reaches_trans _ _ (statelessAt 10) _ _ _ _ _ (reaches_loadDec _ _ _ (offsets + 8) _
    (by simp [stOffsetsGlobal, setVarHOLFinite, evalHOLExact, evalListHOLExact, hg, wordOpHOL, wordOp, valueIsWord,
      valueWord])) ?_
  rintro _ ⟨d8, rfl⟩
  rw [a10]
  refine reaches_trans _ _ (statelessAt 11) _ _ _ _ _ (reaches_alloc96 _ _ _ H code (by simp [setVarHOLFinite, heap])
    pointerBound) ?_
  rintro _ ⟨req, ready, rc, rm, rl, rcode, rd, rg, rfl⟩
  rw [a11]
  have siH : (setVarHOLFinite (ofString "si") (.val (.word H)) ready).locals.lookup (ofString "si") =
      some (.val (.word H)) := by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine reaches_trans _ _ (statelessAt 12) _ _ _ _ _ (reaches_storeWord _ _ le64Slot (H + 88) _
    (by simp [sszLocal, evalHOLExact, evalListHOLExact, siH, wordOpHOL, wordOp, valueIsWord, valueWord])
    (fun v hv => @eval_op_word σ _ (fun a => Classical.propDecidable _) _ _ v hv)) ?_
  rintro _ ⟨x88, _, d88, rfl⟩
  rw [a12]
  refine reaches_trans _ _ (statelessAt 13) _ _ _ _ _ (reaches_decExact _ _ _ (P + memWord s.memory offsets) _
    (by simp [sszLocal, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm, rl, hp, wordOpHOL, wordOp, valueIsWord, valueWord])) ?_
  rintro _ rfl
  rw [a13]
  refine reaches_trans _ _ (statelessAt 14) _ _ _ _ _ (reaches_decExact _ _ _
    (memWord s.memory (offsets + 8) - memWord s.memory offsets) _
    (by simp [sszLocal, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm, rl, hp, wordOpHOL, wordOp, valueIsWord, valueWord])) ?_
  rintro _ rfl
  rw [a14]
  refine reaches_trans _ _ (statelessAt 15) _ _ _ _ _ (reaches_guard _ _ 81 _ (by simp [setVarHOLFinite, rcode, code])) ?_
  rintro _ ⟨rfl, guardOk⟩
  rw [a15]
  refine reaches_trans _ _ (statelessAt 16) _ _ _ _ _ (reaches_decBounded _ _ _ _
    (@le32Base_bounded σ _ (fun a => Classical.propDecidable _) "np")) ?_
  rintro _ ⟨opl, spl, rfl⟩
  rw [a16]
  refine reaches_trans _ _ (statelessAt 17) _ _ _ _ _ (reaches_decBounded _ _ _ _
    (@le32Off_bounded σ _ (fun a => Classical.propDecidable _) "np" 4)) ?_
  rintro _ ⟨ovh, svh, rfl⟩
  rw [a17]
  refine reaches_trans _ _ (statelessAt 18) _ _ _ _ _ (reaches_decBounded _ _ _ _
    (@le32Off_bounded σ _ (fun a => Classical.propDecidable _) "np" 40)) ?_
  rintro _ ⟨orq, srq, rfl⟩
  rw [a18]
  refine reaches_trans _ _ (statelessAt 19) _ _ _ _ _ (reaches_storeWord _ _ _ offsets _ (by simp [stOffsetsGlobal, evalHOLExact, evalListHOLExact, setVarHOLFinite, rg, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs, Ne.symm hs, hg, wordOpHOL, wordOp, valueIsWord, valueWord])
    (fun v hv => ⟨opl, by simp [sszLocal, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm] at hv; exact hv.symm⟩)) ?_
  rintro _ ⟨y0, ev0, dpl, rfl⟩
  rw [a19]
  refine reaches_trans _ _ (statelessAt 20) _ _ _ _ _ (reaches_storeWord _ _ _ (offsets + 8) _ (by simp [stOffsetsGlobal, evalHOLExact, evalListHOLExact, setVarHOLFinite, rg, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs, Ne.symm hs, hg, wordOpHOL, wordOp, valueIsWord, valueWord])
    (fun v hv => ⟨ovh, by simp [sszLocal, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm] at hv; exact hv.symm⟩)) ?_
  rintro _ ⟨y1, ev1, dvh, rfl⟩
  rw [a20]
  refine reaches_trans _ _ (statelessAt 21) _ _ _ _ _ (reaches_storeWord _ _ _ (offsets + 16) _ (by simp [stOffsetsGlobal, evalHOLExact, evalListHOLExact, setVarHOLFinite, rg, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs, Ne.symm hs, hg, wordOpHOL, wordOp, valueIsWord, valueWord])
    (fun v hv => ⟨orq, by simp [sszLocal, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm] at hv; exact hv.symm⟩)) ?_
  rintro _ ⟨y2, ev2, drq, rfl⟩
  simp [sszLocal, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm, rl] at ev0 ev1 ev2
  subst ev0 ev1 ev2
  rw [a21]
  refine reaches_mono _ _ _ _ _ 8 8 (le_refl _) ?_ (reaches_midCheck _ (statelessAt 22) offsets
    (memWord s.memory (offsets + 8) - memWord s.memory offsets) (by simp [setVarHOLFinite, rcode, code])
    (by simp [setVarHOLFinite, rg, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs, Ne.symm hs, hg])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm, rl]))
  rintro E ⟨checked, em, eg, ed, el, ec⟩
  have notShort : ¬ memWord s.memory (offsets + 8) - memWord s.memory offsets < 44 := by
    intro lt
    have one : ∀ (t : PanSemStateFiniteExact 64 σ),
        t.locals.lookup (ofString "nlen") = some (.val (.word (memWord s.memory (offsets + 8) - memWord s.memory offsets))) →
        @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.cmp .lower (sszLocal "nlen") (.const 44)) = some (.val (.word 1)) := by
      intro t ht
      simp [sszLocal, evalHOLExact, ht, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact lt
    rw [one _ (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm, rl])] at guardOk
    simp at guardOk
  have rdom : ∀ a, ready.memaddrs a → s.memaddrs a := fun a h => by rw [rd] at h; exact h
  refine ⟨d0, d8, req, notShort, rdom _ d88, rdom _ drq, x88, opl, ovh, orq, spl, svh, srq, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [em]; show wmem (wmem (wmem (wmem ready.memory (H + 88) x88) offsets opl) (offsets + 8) ovh) (offsets + 16) orq = _
    rw [rm]; rfl
  · rw [eg]; exact rg
  · rw [ed]; exact rd
  · rw [ec]; exact rcode
  all_goals first
    | (rw [el]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm, rl, hp]; done)
    | (intro k k1 k2 k3 k4 k5 k6 k7 k8; rw [el]
       simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nm, rl, Ne.symm k1, Ne.symm k2, Ne.symm k3, Ne.symm k4, Ne.symm k5, Ne.symm k6, Ne.symm k7,
         Ne.symm k8]; done)
    | exact sszCheckOffsetsReturned_congr _ E offsets 3 44 _ _ em.symm ed.symm checked

#print axioms evaluate_stateless_mid
end InitECandidate.Runtime
