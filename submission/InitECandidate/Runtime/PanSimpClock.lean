import Flapjack.Pancake.Proofs.PanSimp.CompileCorrect
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.PanSimp

/-- The full simplifier simulation preserves initial and remaining fuel. -/
theorem pan_simp_same_clock {width : Nat} {σ : Type} [NeZero width] :
    ∀ (prog : ProgHOL width) (s : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width)) (s1 t : PanSemStateFiniteExact width σ),
      evaluateHOLFiniteState s prog = (res, s1) ∧ res ≠ some .error ∧
        stateRel s t t.code →
      ∃ t1, t.clock = s.clock ∧ t1.clock = s1.clock ∧ evaluateHOLFiniteState t (seqAssocHOL .skip prog) = (res, t1) ∧
        stateRel s1 t1 t1.code := by
  intro p s res post target h
  obtain ⟨final,run,related⟩ := Flapjack.PanSimp.compileCorrectHOL p s res post target h
  refine ⟨final,?_,?_,run,related⟩
  · rw [h.2.2.1]
  · rw [related.1]

#print axioms pan_simp_same_clock
end InitECandidate.Runtime
