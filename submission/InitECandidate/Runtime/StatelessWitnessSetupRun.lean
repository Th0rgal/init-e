import InitECandidate.Runtime.StatelessWitnessSetupLoop
import InitECandidate.Runtime.StatelessPrefixRun
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Facts at the actual At35 entry (inside the dec-i scope) after a successful witness setup. -/
def WsEntry {σ : Type} (s E : PanSemStateFiniteExact 64 σ) (WL offsets W0 W1 W2 : BitVec 64) : Prop :=
  ¬ WL < 12 ∧ E.locals.lookup (ofString "i") = some (.val (.word 3)) ∧
  (∀ k, k ≠ ofString "i" → E.locals.lookup k = s.locals.lookup k) ∧
  E.globals = s.globals ∧ E.memaddrs = s.memaddrs ∧ E.code = s.code ∧ 3 ≤ s.clock ∧ E.clock = s.clock - 3 ∧
  W0.toNat < 2 ^ 32 ∧ W1.toNat < 2 ^ 32 ∧ W2.toNat < 2 ^ 32 ∧
  s.memaddrs offsets ∧ s.memaddrs (offsets + 8) ∧ s.memaddrs (offsets + 16) ∧
  E.memory = wmem (wmem (wmem s.memory offsets W0) (offsets + 8) W1) (offsets + 16) W2

theorem stAbort_clock {σ : Type} (s t : PanSemStateFiniteExact 64 σ) out (K j : Nat) (tc : t.clock + j = s.clock)
    (h : StAbort t out K) : StAbort s out (K + j) := by
  obtain ⟨x, h1, h2, h3, h4, h5⟩ := h
  exact ⟨x, h1, h2, by omega, by omega, fun k => h5 (by omega)⟩

theorem stAbort_restore {σ : Type} (s : PanSemStateFiniteExact 64 σ) (o : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (K : Nat) (h : StAbort s o K) :
    StAbort s (o.1, ({o.2 with locals := L} : PanSemStateFiniteExact 64 σ)) K := by
  obtain ⟨x, h1, h2, h3, h4, h5⟩ := h
  exact ⟨x, h1, h2, h3, h4, h5⟩

theorem evaluate_stateless_witness_setup {σ : Type} (s : PanSemStateFiniteExact 64 σ) (WL offsets : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hwl : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))) :
    (∃ E W0 W1 W2, WsEntry s E WL offsets W0 W1 W2 ∧
      evaluateHOLFiniteState s (statelessAt 32) =
        (let o := evaluateHOLFiniteState E (statelessAt 35)
         (o.1, {o.2 with locals := o.2.locals.resVarEq (ofString "i", s.locals.lookup (ofString "i"))}))) ∨
    StAbort s (evaluateHOLFiniteState s (statelessAt 32)) 3 := by
  obtain ⟨a32, a33, a34⟩ := source_stateless_witness_setup
  rw [a32]
  rcases stGuard_cases s _ 82 code with ⟨c0, r0⟩ | ab
  · have notShort : ¬ WL < 12 := by
      intro lt
      have one : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .lower (sszLocal "wlen") (.const 12)) = some (.val (.word 1)) := by
        simp [sszLocal, evalHOLExact, hwl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact lt
      rw [one] at c0; simp at c0
    rw [seq_none_eq _ _ _ _ (by unfold wsGuard; exact r0), a33, evaluateHOLFiniteState_dec_total]
    dsimp only
    simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
    rw [a34]
    generalize hq : setVarHOLFinite (ofString "i") (.val (.word 0#64)) s = q
    have qi : q.locals.lookup (ofString "i") = some (.val (.word 0)) := by
      rw [← hq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have qg : q.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by rw [← hq]; exact hg
    have qc : q.clock = s.clock := by rw [← hq]; rfl
    have abortQ : ∀ j, StAbort q (evaluateHOLFiniteState q wsLoop) j → j ≤ 3 →
        StAbort s ((evaluateHOLFiniteState q (.seq wsLoop (statelessAt 35))).1,
          {(evaluateHOLFiniteState q (.seq wsLoop (statelessAt 35))).2 with
            locals := (evaluateHOLFiniteState q (.seq wsLoop (statelessAt 35))).2.locals.resVarEq
              (ofString "i", s.locals.lookup (ofString "i"))}) 3 := by
      intro j h hj
      apply stAbort_restore
      exact stAbort_mono s _ (j + 0) 3 (by omega) (stAbort_clock s q _ j 0 (by omega)
        (stAbort_seq q wsLoop (statelessAt 35) j h))
    rcases wsLoop_iter q 0 offsets (by decide) qi qg with ab0 | ⟨nz0, x0, small0, dom0, run0⟩
    · exact Or.inr (abortQ 1 ab0 (by omega))
    · generalize hq1 : setVarHOLFinite (ofString "i") (.val (.word (0 + 1)))
        ({decClockHOLFinite q with memory := wmem q.memory (offsets + 0 * 8) x0} : PanSemStateFiniteExact 64 σ) = q1 at run0
      have q1i : q1.locals.lookup (ofString "i") = some (.val (.word 1)) := by
        rw [← hq1]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have q1g : q1.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by rw [← hq1]; exact qg
      have q1c : q1.clock + 1 = q.clock := by rw [← hq1]; show q.clock - 1 + 1 = q.clock; omega
      rcases wsLoop_iter q1 1 offsets (by decide) q1i q1g with ab1 | ⟨nz1, x1, small1, dom1, run1⟩
      · refine Or.inr (abortQ 2 ?_ (by omega))
        rw [run0]; exact stAbort_clock q q1 _ 1 1 q1c ab1
      · generalize hq2 : setVarHOLFinite (ofString "i") (.val (.word (1 + 1)))
          ({decClockHOLFinite q1 with memory := wmem q1.memory (offsets + 1 * 8) x1} : PanSemStateFiniteExact 64 σ) = q2 at run1
        have q2i : q2.locals.lookup (ofString "i") = some (.val (.word 2)) := by
          rw [← hq2]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have q2g : q2.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by rw [← hq2]; exact q1g
        have q2c : q2.clock + 1 = q1.clock := by rw [← hq2]; show q1.clock - 1 + 1 = q1.clock; omega
        rcases wsLoop_iter q2 2 offsets (by decide) q2i q2g with ab2 | ⟨nz2, x2, small2, dom2, run2⟩
        · refine Or.inr (abortQ 3 ?_ (by omega))
          rw [run0, run1]; exact stAbort_clock q q2 _ 1 2 (by omega) ab2
        · generalize hq3 : setVarHOLFinite (ofString "i") (.val (.word (2 + 1)))
            ({decClockHOLFinite q2 with memory := wmem q2.memory (offsets + 2 * 8) x2} : PanSemStateFiniteExact 64 σ) = q3 at run2
          have q3i : q3.locals.lookup (ofString "i") = some (.val (.word 3)) := by
            rw [← hq3]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have q3c : q3.clock + 1 = q2.clock := by rw [← hq3]; show q2.clock - 1 + 1 = q2.clock; omega
          have exit := wsLoop_exit q3 q3i
          have e0 : offsets + 0 * 8 = offsets := by simp
          have e1 : offsets + 1 * 8 = offsets + 8 := by simp
          have e2 : offsets + 2 * 8 = offsets + 16 := by simp
          left
          refine ⟨q3, x0, x1, x2, ⟨notShort, q3i, ?_, ?_, ?_, ?_, by omega, by omega, small0, small1, small2, ?_, ?_, ?_, ?_⟩, ?_⟩
          · intro k hk
            rw [← hq3, ← hq2, ← hq1, ← hq]
            simp [setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · rw [← hq3, ← hq2, ← hq1, ← hq]; rfl
          · rw [← hq3, ← hq2, ← hq1, ← hq]; rfl
          · rw [← hq3, ← hq2, ← hq1, ← hq]; rfl
          · rw [← hq, e0] at dom0; exact dom0
          · rw [← hq1, ← hq, e1] at dom1; exact dom1
          · rw [← hq2, ← hq1, ← hq, e2] at dom2; exact dom2
          · rw [← hq3, ← hq2, ← hq1, ← hq]
            show wmem (wmem (wmem s.memory (offsets + 0 * 8) x0) (offsets + 1 * 8) x1) (offsets + 2 * 8) x2 = _
            rw [e0, e1, e2]
          · rw [evaluateHOLFiniteState_seq_line780, run0, run1, run2, exit]
  · exact Or.inr (stAbort_mono s _ 1 3 (by omega) (stAbort_seq s wsGuard (statelessAt 33) 1 ab))

#print axioms evaluate_stateless_witness_setup
end InitECandidate.Runtime
