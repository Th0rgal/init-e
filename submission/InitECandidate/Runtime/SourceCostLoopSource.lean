import InitECandidate.Runtime.SourceCostCrepControl
import InitECandidate.Runtime.SourceCostLoopControl
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The pinned Pan-to-Crep result relation never relates a non-error source
result to a Crep `Error`. -/
theorem resultRel_not_error {F : Type} {context : PanToCrepContextExact 64}
    {post : PanSemStateFiniteExact 64 F} {t1 : CrepSemHOLState 64 F}
    {r : Option (PanSemResultExact 64)} {r1 : Option (CrepResultHOLExact 64)}
    (rel : pcCompileCorrectResultRel context post t1 r r1) : r1 ≠ some .error := by
  intro h
  subst h
  rcases r with _ | r
  · simp [pcCompileCorrectResultRel] at rel
  · cases r with
    | exception eid v =>
      simp only [pcCompileCorrectResultRel] at rel
      split at rel
      · exact rel
      · simp at rel
    | _ => simp [pcCompileCorrectResultRel] at rel

/-- Statement-level composition of the two executed-work transfers: the
selected source trace's events, weighted by `sourceCrepWeights`, pay seven
times over for the actual execution of the Loop code that `crep_to_loop`
compiles from the `pan_to_crep` output, from a clock extension at which all
original `ncompile_correct` conclusions hold. Conditional on the named
temporary `LoopOptimiseWork` contract for callee bodies; preprocessing
(`pan_simp`, `pan_structs`, `pan_globals`, `crep_arith`) is not covered here. -/
theorem source_loop_executed_work {F : Type} (opt : LoopOptimiseWork)
    {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) (t : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64) (resultOk : r ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : bulkLoadSitesProg p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) → bulkLoadSitesProg body = true)
    (u : LoopSemStateFiniteExact 64 F) (loopContext : CrepToLoopContextExact) (live : NumSet)
    (loopRel : CrepLoopRel loopContext live t u) :
    ∃ extra wl,
      LoopWork { u with clock := u.clock + extra }
        (compileHOLExact loopContext live (compileProgExactHOLW context p))
        (evaluate (compileHOLExact loopContext live (compileProgExactHOLW context p))
          { u with clock := u.clock + extra }) wl ∧
      wl ≤ 7 * sourceCrepWeights.score (executionWork events) ∧
      LoopRunRel loopContext live (evalCrepSemHOLProgExact t (compileProgExactHOLW context p))
        (evaluate (compileHOLExact loopContext live (compileProgExactHOLW context p))
          { u with clock := u.clock + extra }) := by
  obtain ⟨w, crepWork, crepBound⟩ := source_crep_executed_work run t context resultOk rel
    localised checked codeChecked
  obtain ⟨r1, t1, crepRun, _, _, _, resultRel⟩ := compiled_source_run t context run.sound
    resultOk rel.state rel.code rel.exceptions rel.locals localised
  have ok : (evalCrepSemHOLProgExact t (compileProgExactHOLW context p)).1 ≠ some .error := by
    rw [crepRun]; exact resultRel_not_error resultRel
  obtain ⟨extra, wl, work, bound, runRel⟩ :=
    crep_loop_executed_work opt crepWork u loopContext live ok loopRel
  exact ⟨extra, wl, work, by omega, runRel⟩

#print axioms resultRel_not_error
#print axioms source_loop_executed_work
end InitECandidate.Runtime.FineCost
