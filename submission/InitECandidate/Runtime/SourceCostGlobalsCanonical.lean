import InitECandidate.Runtime.SourceCostGlobalsRun
import InitECandidate.Runtime.PanSharpCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Functional cost transfer through the actual globals compiler. The source
trace is the total canonical trace; no chosen cost witness is a premise. -/

theorem sourceExecutionEvents_globals_le {F : Type} (B : Nat)
    (s t : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (context : PanGlobalsContextExact 64)
    (ok : (evaluateHOLFiniteState s p).1 ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true context s t)
    (ready : globalsReadyProg p = true) (code : GlobalsCodeReady s.code)
    (noTemp : s.locals.lookup globalsTemp = none) (covered : GlobalsCovered context s) :
    sharpSourceScore B (sourceExecutionEvents t (compileProgExactHOL context p)) ≤
      sharpSourceScore B (sourceExecutionEvents s p) := by
  obtain ⟨post, events, run, _, price⟩ := globals_compile_run B
    (sourceExecutionEvents_run s p) ok context t rel ready code noTemp covered
  rw [sourceExecutionEvents_eq_of_run run]
  exact price

/-- Globals preprocessing introduces no multiplicative loss in the canonical
sharp source cost. This is a statement-level result; initialization and actual
installed-program entry still need their separate compiler relations. -/
theorem sourceSharpExecutionCost_globals_le {F : Type}
    (s t : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (context : PanGlobalsContextExact 64)
    (ok : (evaluateHOLFiniteState s p).1 ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true context s t)
    (ready : globalsReadyProg p = true) (code : GlobalsCodeReady s.code)
    (noTemp : s.locals.lookup globalsTemp = none) (covered : GlobalsCovered context s) :
    sourceSharpExecutionCost t (compileProgExactHOL context p) ≤
      sourceSharpExecutionCost s p :=
  sourceExecutionEvents_globals_le sharpReplayBound s t p context ok rel ready code noTemp covered

#print axioms sourceExecutionEvents_globals_le
#print axioms sourceSharpExecutionCost_globals_le
end InitECandidate.Runtime.FineCost
