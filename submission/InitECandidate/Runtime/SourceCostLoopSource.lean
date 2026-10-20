import InitECandidate.Runtime.SourceCostCrepControl
import InitECandidate.Runtime.SourceCostLoopPricing
import InitECandidate.Runtime.SourceCostCrepSimp
import InitECandidate.Runtime.SourceCostLoopOptimise
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
    crep_loop_coarse_work opt crepWork u loopContext live ok loopRel
  exact ⟨extra, wl, work, by omega, runRel⟩

/-- As `source_loop_executed_work`, but through the `crep_arith$simp_prog`
pass that `crep_to_loop$compile_prog` applies first: the Loop code is
`compile (simp_prog (pan_to_crep p))`, run against the `simp_prog`-mapped Crep
state, as in the installed per-function code. Still conditional on the named
`LoopOptimiseWork` contract. -/
theorem source_simp_loop_executed_work {F : Type} (opt : LoopOptimiseWork)
    {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) (t : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64) (resultOk : r ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : bulkLoadSitesProg p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) → bulkLoadSitesProg body = true)
    (u : LoopSemStateFiniteExact 64 F) (loopContext : CrepToLoopContextExact) (live : NumSet)
    (loopRel : CrepLoopRel loopContext live (crepSimpMapcsHOL t) u) :
    ∃ extra wl,
      LoopWork { u with clock := u.clock + extra }
        (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) wl ∧
      wl ≤ 7 * sourceCrepWeights.score (executionWork events) ∧
      LoopRunRel loopContext live
        (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) := by
  obtain ⟨w, crepWork, crepBound⟩ := source_crep_executed_work run t context resultOk rel
    localised checked codeChecked
  obtain ⟨r1, t1, crepRun, _, _, _, resultRel⟩ := compiled_source_run t context run.sound
    resultOk rel.state rel.code rel.exceptions rel.locals localised
  have ok : (evalCrepSemHOLProgExact t (compileProgExactHOLW context p)).1 ≠ some .error := by
    rw [crepRun]; exact resultRel_not_error resultRel
  obtain ⟨ws, simpWork, simpBound⟩ := crep_simp_work crepWork ok
  have simpOk : (evalCrepSemHOLProgExact (crepSimpMapcsHOL t)
      (crepSimpProgHOL (compileProgExactHOLW context p))).1 ≠ some .error := by
    rw [crepArithSimpProgCorrect _ t r1 t1 crepRun (resultRel_not_error resultRel)]
    exact resultRel_not_error resultRel
  obtain ⟨extra, wl, work, bound, runRel⟩ :=
    crep_loop_coarse_work opt simpWork u loopContext live simpOk loopRel
  exact ⟨extra, wl, work, by omega, runRel⟩

/-- The temporary `LoopOptimiseWork` contract, discharged by root's
`loop_optimise_executed_work` (coefficient one). -/
theorem loop_optimise_work : LoopOptimiseWork :=
  fun F q s r post w work nonerror noBreak noContinue =>
    loop_optimise_executed_work F q s r post w work nonerror noBreak noContinue

/-- Unconditional Crep-to-Loop executed-work transfer. -/
theorem crep_loop_installed_work {F : Type} {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64}
    {w : Nat} (work : CrepWork t p w) (u : LoopSemStateFiniteExact 64 F)
    (context : CrepToLoopContextExact) (live : NumSet)
    (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error) (rel : CrepLoopRel context live t u) :
    LoopPaid context live t u p (7 * w) :=
  crep_loop_coarse_work loop_optimise_work work u context live ok rel

/-- Unconditional Crep-to-Loop transfer at exact Loop prices, factor one. -/
theorem crep_loop_installed_sharp_work {F : Type} {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64}
    {w : Nat} (work : CrepWorkL sharpPricing t p w) (u : LoopSemStateFiniteExact 64 F)
    (context : CrepToLoopContextExact) (live : NumSet)
    (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error) (rel : CrepLoopRel context live t u) :
    LoopPaid context live t u p w :=
  crep_loop_sharp_work loop_optimise_work work u context live ok rel

/-- Unconditional statement-level composition source -> pan_to_crep ->
simp_prog -> crep_to_loop, against the installed-code Crep state. The source
program is the one `pan_to_crep` receives; the `pan_simp`/`pan_structs`/
`pan_globals` preprocessing transfers are separate. -/
theorem source_simp_loop_installed_work {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) (t : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64) (resultOk : r ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : bulkLoadSitesProg p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) → bulkLoadSitesProg body = true)
    (u : LoopSemStateFiniteExact 64 F) (loopContext : CrepToLoopContextExact) (live : NumSet)
    (loopRel : CrepLoopRel loopContext live (crepSimpMapcsHOL t) u) :
    ∃ extra wl,
      LoopWork { u with clock := u.clock + extra }
        (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) wl ∧
      wl ≤ 7 * sourceCrepWeights.score (executionWork events) ∧
      LoopRunRel loopContext live
        (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          { u with clock := u.clock + extra }) :=
  source_simp_loop_executed_work loop_optimise_work run t context resultOk rel localised checked
    codeChecked u loopContext live loopRel

#print axioms loop_optimise_work
#print axioms crep_loop_installed_work
#print axioms crep_loop_installed_sharp_work
#print axioms source_simp_loop_installed_work
#print axioms resultRel_not_error
#print axioms source_simp_loop_executed_work
#print axioms source_loop_executed_work
end InitECandidate.Runtime.FineCost
