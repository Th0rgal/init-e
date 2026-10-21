import InitECandidate.Runtime.SourceCostSharpSource
import InitECandidate.Runtime.PanCostDeterminism
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.PanSemStateFiniteExact

/-- Canonical finite Pancake execution cost at the checked sharp compiler
prices. Address replay is charged per actual multiword operation, not by a
whole-program expression-size multiplier. -/
noncomputable def sourceSharpExecutionCost {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : Nat :=
  sharpScore (sourceExecutionEvents s p)

/-- Any concrete guest trace computes the canonical cost, independently of the
choice used to select the total source execution witness. -/
theorem sourceSharpExecutionCost_eq_of_run {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) :
    sourceSharpExecutionCost s p = sharpScore events := by
  unfold sourceSharpExecutionCost
  rw [sourceExecutionEvents_eq_of_run run]

/-- The selected source cost bounds the actual simplified-Crep-to-Loop run.
The original semantic/compiler relations and static load-site certificates
remain explicit. Structures/globals preprocessing is not asserted here. -/
theorem sourceSharpExecutionCost_pays_loop {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) (t : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64)
    (resultOk : (evaluateHOLFiniteState s p).1 ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : sharpSitesProg sharpReplayBound p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) →
        sharpSitesProg sharpReplayBound body = true)
    (u : LoopSemStateFiniteExact 64 F) (loopContext : CrepToLoopContextExact) (live : NumSet)
    (loopRel : CrepLoopRel loopContext live (crepSimpMapcsHOL t) u) :
    ∃ extra wl,
      LoopWork {u with clock := u.clock + extra}
        (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          {u with clock := u.clock + extra}) wl ∧
      wl ≤ sourceSharpExecutionCost s p ∧
      LoopRunRel loopContext live
        (evalCrepSemHOLProgExact (crepSimpMapcsHOL t) (crepSimpProgHOL (compileProgExactHOLW context p)))
        (evaluate (compileHOLExact loopContext live (crepSimpProgHOL (compileProgExactHOLW context p)))
          {u with clock := u.clock + extra}) :=
  source_loop_sharp_work (sourceExecutionEvents_run s p) t context resultOk rel localised checked
    codeChecked u loopContext live loopRel

#print axioms sourceSharpExecutionCost_eq_of_run
#print axioms sourceSharpExecutionCost_pays_loop
end InitECandidate.Runtime.FineCost
