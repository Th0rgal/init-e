import InitECandidate.Runtime.StatelessPrefixStages
import InitECandidate.Runtime.DecodeRequestsReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Facts at the actual At8 continuation entry after a successful stateless prefix. -/
def StPrefixEntry {σ : Type} (s E : PanSemStateFiniteExact 64 σ) (P L offsets O0 O1 : BitVec 64) : Prop :=
  ¬ L < 2 ∧
  @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) stMagicCond = some (.val (.word 0)) ∧
  ¬ L - 2 < 16 ∧
  E.locals = (s.locals.update (ofString "p", .val (.word (P + 2)))).update (ofString "len", .val (.word (L - 2))) ∧
  E.globals = s.globals ∧ E.memaddrs = s.memaddrs ∧ E.code = s.code ∧
  O0.toNat < 2 ^ 32 ∧ O1.toNat < 2 ^ 32 ∧ s.memaddrs offsets ∧ s.memaddrs (offsets + 8) ∧
  E.memory = wmem (wmem s.memory offsets O0) (offsets + 8) O1 ∧
  SszCheckOffsetsReturned E offsets 2 16 (L - 2) (.val (.word 0))

theorem stGuard_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x c : BitVec 64)
    (hx : s.locals.lookup (ofString "len") = some (.val (.word x)))
    (h : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (sszLocal "len") (.const c)) = some (.val (.word 0))) : ¬ x < c := by
  intro lt
  have one : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (sszLocal "len") (.const c)) = some (.val (.word 1)) := by
    simp [sszLocal, evalHOLExact, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, lt]
  rw [one] at h; simp at h

theorem seq_none_eq {σ : Type} (s t : PanSemStateFiniteExact 64 σ) (first rest : ProgHOL 64)
    (h : evaluateHOLFiniteState s first = (none, t)) :
    evaluateHOLFiniteState s (.seq first rest) = evaluateHOLFiniteState t rest := by
  rw [evaluateHOLFiniteState_seq_line780, h]

/-- The actual original decode_stateless_input prefix At0..At7, at every clock:
either it reaches the At8 continuation entry within six ticks with the guard,
pointer/length, offset-table and offset-check facts, or it aborts without
returning within six ticks (timeout-free with six ticks). -/
theorem evaluate_stateless_prefix {σ : Type} (s : PanSemStateFiniteExact 64 σ) (P L offsets : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))) :
    (∃ E O0 O1, StPrefixEntry s E P L offsets O0 O1 ∧
      evaluateHOLFiniteState s (statelessAt 0) = evaluateHOLFiniteState E (statelessAt 8) ∧
      s.clock ≤ E.clock + 6 ∧ E.clock ≤ s.clock) ∨
    StAbort s (evaluateHOLFiniteState s (statelessAt 0)) 6 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := source_stateless_prefix
  have np : ofString "len" ≠ ofString "p" := by decide_cbv
  rw [a0]
  rcases stGuard_cases s _ 1 code with ⟨c0, r0⟩ | ab
  · rw [seq_none_eq _ _ _ _ (by unfold stGuard0; exact r0), a1]
    rcases stGuard_cases s stMagicCond 2 code with ⟨c1, r1⟩ | ab
    · rw [seq_none_eq _ _ _ _ (by unfold stGuard1; exact r1), a2]
      have r2 : evaluateHOLFiniteState s stAssignP = (none, setVarHOLFinite (ofString "p") (.val (.word (P + 2))) s) := by
        simp [stAssignP, sszLocal, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hp,
          lookupKvarHOLExact, isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, wordOpHOL, wordOp,
          valueIsWord, valueWord]
      rw [seq_none_eq _ _ _ _ r2, a3]
      generalize hs1 : setVarHOLFinite (ofString "p") (.val (.word (P + 2))) s = s1
      have s1L : s1.locals.lookup (ofString "len") = some (.val (.word L)) := by
        rw [← hs1]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, np, Ne.symm np, hL]
      have r3 : evaluateHOLFiniteState s1 stAssignLen =
          (none, setVarHOLFinite (ofString "len") (.val (.word (L - 2))) s1) := by
        simp [stAssignLen, sszLocal, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, s1L,
          lookupKvarHOLExact, isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, wordOpHOL, wordOp,
          valueIsWord, valueWord]
      rw [seq_none_eq _ _ _ _ r3, a4]
      generalize hs2 : setVarHOLFinite (ofString "len") (.val (.word (L - 2))) s1 = s2
      have s2L : s2.locals.lookup (ofString "len") = some (.val (.word (L - 2))) := by
        rw [← hs2]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have s2P : s2.locals.lookup (ofString "p") = some (.val (.word (P + 2))) := by
        rw [← hs2, ← hs1]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, np, Ne.symm np]
      have s2c : s2.clock = s.clock := by rw [← hs2, ← hs1]; rfl
      have s2g : s2.globals = s.globals := by rw [← hs2, ← hs1]; rfl
      have s2d : s2.memaddrs = s.memaddrs := by rw [← hs2, ← hs1]; rfl
      have s2m : s2.memory = s.memory := by rw [← hs2, ← hs1]; rfl
      have s2code : s2.code = originalRuntimeCode := by rw [← hs2, ← hs1]; exact code
      have s2locals : s2.locals = (s.locals.update (ofString "p", .val (.word (P + 2)))).update
          (ofString "len", .val (.word (L - 2))) := by rw [← hs2, ← hs1]; rfl
      rcases stGuard_cases s2 _ 80 s2code with ⟨c4, r4⟩ | ab
      · rw [seq_none_eq _ _ _ _ (by unfold stGuard4; exact r4), a5]
        have d0 : @evalHOLExact 64 σ _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x)) stOffsetsGlobal =
            some (.val (.word offsets)) := by simp [stOffsetsGlobal, evalHOLExact, s2g, hg]
        rcases stStore_cases s2 _ sszSplitFirst offsets d0 (@sszSplitFirst_bounded σ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))) with ⟨O0, small0, dom0, r5⟩ | ab
        · rw [seq_none_eq _ _ _ _ (by unfold stStore0; exact r5), a6]
          generalize hs3 : ({s2 with memory := wmem s2.memory offsets O0} : PanSemStateFiniteExact 64 σ) = s3
          have d1 : @evalHOLExact 64 σ _ s3.toExact (fun x => Classical.propDecidable (s3.memaddrs x))
              (.op .add [stOffsetsGlobal, .const 8]) = some (.val (.word (offsets + 8))) := by
            rw [← hs3]
            simp [stOffsetsGlobal, evalHOLExact, evalListHOLExact, s2g, hg, wordOpHOL, wordOp, valueIsWord, valueWord]
          rcases stStore_cases s3 _ stSecondRead (offsets + 8) d1 (@stSecondRead_bounded σ s3.toExact (fun x => Classical.propDecidable (s3.memaddrs x))) with ⟨O1, small1, dom1, r6⟩ | ab
          · rw [seq_none_eq _ _ _ _ (by unfold stStore1; exact r6), a7]
            generalize hs4 : ({s3 with memory := wmem s3.memory (offsets + 8) O1} : PanSemStateFiniteExact 64 σ) = s4
            have s3d : s3.memaddrs = s.memaddrs := by rw [← hs3, s2d]
            have s4c : s4.clock = s.clock := by rw [← hs4, ← hs3, s2c]
            have s4g : s4.globals = s.globals := by rw [← hs4, ← hs3, s2g]
            have s4d : s4.memaddrs = s.memaddrs := by rw [← hs4, ← hs3, s2d]
            have s4m : s4.memory = wmem (wmem s.memory offsets O0) (offsets + 8) O1 := by rw [← hs4, ← hs3, s2m]
            have s4code : s4.code = originalRuntimeCode := by rw [← hs4, ← hs3]; exact s2code
            have s4L : s4.locals.lookup (ofString "len") = some (.val (.word (L - 2))) := by
              rw [← hs4, ← hs3]; exact s2L
            have args : evalListHOLFinite s4 (h := fun address => Classical.propDecidable (s4.memaddrs address))
                [stOffsetsGlobal, .const 2, .const 16, sszLocal "len"] =
                some [.val (.word offsets), .val (.word 2), .val (.word 16), .val (.word (L - 2))] := by
              simp [stOffsetsGlobal, sszLocal, evalListHOLFinite, evalListHOLExact, evalHOLExact, s4g, hg, s4L]
            have lower := evaluateHOLFiniteState_clock_le s4 stCheck
            have bounded := fun (en : 6 ≤ s4.clock) =>
              evaluate_sszCheckOffsets_call_bounded s4 none _ offsets 2 16 (L - 2) args s4code (by decide) en
            have nr := evaluate_discard_call_no_return s4 (ofString "ssz_check_offsets")
              [stOffsetsGlobal, .const 2, .const 16, sszLocal "len"]
            cases run : evaluateHOLFiniteState s4 stCheck with
            | mk r E =>
              rw [run] at lower
              replace lower : E.clock ≤ s4.clock := lower
              have bounded' : 6 ≤ s4.clock → s4.clock ≤ E.clock + 6 ∧ r ≠ some .timeOut := by
                intro en; have b := bounded en; unfold stCheck at run; rw [run] at b
                exact ⟨b.1, b.2.2⟩
              cases r with
              | none =>
                left
                obtain ⟨checked, em, eg, ed, el⟩ := sszCheckOffsets_call_returned s4 _ offsets 2 16 (L - 2) args s4code
                  (by decide) E (by unfold stCheck at run; exact run)
                have eCode : E.code = originalRuntimeCode := by
                  have mt := evaluateHOLFiniteState_metadata s4 stCheck
                  rw [run] at mt; exact mt.1.trans s4code
                refine ⟨E, O0, O1, ⟨stGuard_word s L 2 hL c0, c1, stGuard_word s2 (L - 2) 16 s2L c4,
                  by rw [el, ← hs4, ← hs3, s2locals], by rw [eg, s4g], by rw [ed, s4d], by rw [eCode, code],
                  small0, small1, by rw [← s2d]; exact dom0, by rw [← s3d]; exact dom1, by rw [em, s4m],
                  sszCheckOffsetsReturned_congr s4 E offsets 2 16 (L - 2) _ em.symm ed.symm checked⟩,
                  by rw [seq_none_eq _ _ _ _ run], ?_, by omega⟩
                by_cases en : 6 ≤ s4.clock
                · have := (bounded' en).1; omega
                · omega
              | some x =>
                right
                rw [evaluateHOLFiniteState_seq_line780, run]
                dsimp only
                refine ⟨x, rfl, fun v h => nr v (by unfold stCheck at run; rw [run, h]), ?_, ?_, ?_⟩
                · show s.clock ≤ E.clock + 6
                  by_cases en : 6 ≤ s4.clock
                  · have := (bounded' en).1; omega
                  · omega
                · show E.clock ≤ s.clock
                  omega
                · intro en h
                  exact (bounded' (by omega)).2 (by rw [h])
          · right
            refine stAbort_mono s _ 0 6 (by omega) ?_
            have : s3.clock = s.clock := by rw [← hs3, s2c]
            obtain ⟨x, h1, h2, h3, h4, h5⟩ := stAbort_seq s3 stStore1 (statelessAt 7) 0 ab
            exact ⟨x, h1, h2, by omega, by omega, fun _ => h5 (by omega)⟩
        · right
          refine stAbort_mono s _ 0 6 (by omega) ?_
          obtain ⟨x, h1, h2, h3, h4, h5⟩ := stAbort_seq s2 stStore0 (statelessAt 6) 0 ab
          exact ⟨x, h1, h2, by omega, by omega, fun _ => h5 (by omega)⟩
      · right
        refine stAbort_mono s _ 1 6 (by omega) ?_
        obtain ⟨x, h1, h2, h3, h4, h5⟩ := stAbort_seq s2 stGuard4 (statelessAt 5) 1 ab
        exact ⟨x, h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
    · exact Or.inr (stAbort_mono s _ 1 6 (by omega) (stAbort_seq s stGuard1 (statelessAt 2) 1 ab))
  · exact Or.inr (stAbort_mono s _ 1 6 (by omega) (stAbort_seq s stGuard0 (statelessAt 1) 1 ab))

#print axioms evaluate_stateless_prefix

/-- A returned stateless-input run passes through the At8 continuation entry. -/
theorem stateless_prefix_returned {σ : Type} (s post : PanSemStateFiniteExact 64 σ) (P L offsets : BitVec 64)
    (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (run : evaluateHOLFiniteState s (statelessAt 0) = (some (.returned v), post)) :
    ∃ E O0 O1, StPrefixEntry s E P L offsets O0 O1 ∧
      evaluateHOLFiniteState E (statelessAt 8) = (some (.returned v), post) ∧
      s.clock ≤ E.clock + 6 ∧ E.clock ≤ s.clock := by
  rcases evaluate_stateless_prefix s P L offsets code hp hL hg with ⟨E, O0, O1, entry, eq, c1, c2⟩ | ⟨x, h1, h2, _⟩
  · exact ⟨E, O0, O1, entry, eq ▸ run, c1, c2⟩
  · rw [run] at h1
    exact absurd (Option.some.inj h1).symm (h2 v)

#print axioms stateless_prefix_returned
end InitECandidate.Runtime
