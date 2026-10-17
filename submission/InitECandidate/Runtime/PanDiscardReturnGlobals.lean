import InitECandidate.Runtime.ReadOnlyGlobals
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Returning after a discard call exposes its normal completion and
preserves its globals through a read-only continuation. -/
theorem evaluate_discard_then_return_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (value : ValueHOL 64)
    (supported : readOnlyMemory tail = true)
    (run : evaluateHOLFiniteState state (.seq (.call (some (none,none)) function arguments) tail) =
      (some (.returned value),post)) :
    ∃ middle, evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,middle) ∧
      post.globals = middle.globals := by
  have noReturn := evaluate_discard_call_no_return state function arguments value
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state (.call (some (none,none)) function arguments) with
  | mk result middle =>
    rw [called] at run noReturn
    cases result with
    | some stopped => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      dsimp only at run
      have globals := evaluate_readOnly_globals tail supported middle
      rw [run] at globals
      exact ⟨middle,rfl,globals⟩

#print axioms evaluate_discard_then_return_globals
end InitECandidate.Runtime
