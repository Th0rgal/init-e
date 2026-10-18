import InitECandidate.Runtime.SszCheckOffsetsLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The final first-offset check: at most one clock, terminal, and a return
is 0 with offs[0] readable and equal to fixed. -/
theorem evaluate_sszCheckFinal {σ : Type} (p : PanSemStateFiniteExact 64 σ) (offs fixed : BitVec 64)
    (code : p.code = originalRuntimeCode)
    (hoffs : p.locals.lookup (ofString "offs") = some (.val (.word offs)))
    (hfixed : p.locals.lookup (ofString "fixed") = some (.val (.word fixed))) (positive : p.clock ≠ 0) :
    let out := evaluateHOLFiniteState p sszCheckFinal
    p.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ p.clock ∧ out.1 ≠ none ∧ out.1 ≠ some .timeOut ∧
      (∀ v, out.1 = some (.returned v) → v = .val (.word 0) ∧ p.memaddrs offs ∧ memWord p.memory offs = fixed) := by
  unfold sszCheckFinal
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  by_cases dom : p.memaddrs offs
  · by_cases eq : memWord p.memory offs = fixed
    · have cond : @evalHOLExact 64 σ _ p.toExact (fun a => Classical.propDecidable (p.memaddrs a))
          (.cmp .notEqual (.load .one (.var .local (ofString "offs"))) (.var .local (ofString "fixed"))) =
          some (.val (.word 0#64)) := by
        simp [evalHOLExact, hoffs, hfixed, memLoadHOLExact, isWfShapeExactHOL, dom,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact eq
      rw [cond]
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
        emptyLocalsHOLFinite, dom, eq]
    · have cond : @evalHOLExact 64 σ _ p.toExact (fun a => Classical.propDecidable (p.memaddrs a))
          (.cmp .notEqual (.load .one (.var .local (ofString "offs"))) (.var .local (ofString "fixed"))) =
          some (.val (.word 1#64)) := by
        simp [evalHOLExact, hoffs, hfixed, memLoadHOLExact, isWfShapeExactHOL, dom,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact eq
      rw [cond]
      obtain ⟨x, run, abnormal, c1, c2⟩ := sszFail_abnormal p 12 code positive
      simp only [show (1#64 : BitVec 64) ≠ 0 by decide, if_false]
      rw [run]
      dsimp only
      refine ⟨c1, c2, by rw [run]; simp, fun h => abnormal.2.1 (Option.some.inj (run.symm.trans h)), fun v h => absurd (Option.some.inj (run.symm.trans h)) (abnormal.2.2.2 v)⟩
  · have cond : @evalHOLExact 64 σ _ p.toExact (fun a => Classical.propDecidable (p.memaddrs a))
        (.cmp .notEqual (.load .one (.var .local (ofString "offs"))) (.var .local (ofString "fixed"))) = none := by
      simp [evalHOLExact, hoffs, hfixed, memLoadHOLExact, isWfShapeExactHOL, dom]
    rw [cond]
    simp

#print axioms evaluate_sszCheckFinal
end InitECandidate.Runtime
