import InitECandidate.Runtime.RlpDecodeFullyContinuation
import InitECandidate.Runtime.RlpErrorCheckFlow
import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successfully returned full-decode check leaves the entire global map
unchanged, without a local-shape or clock premise. -/
theorem rlpDecodeFully_continuation_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpDecodeFullyContinuation = (some (.returned value),post)) :
    post.globals = state.globals := by
  obtain ⟨result,middle,checked,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
    (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len"))) 6 code
  rw [source_rlpDecodeFully_continuation,evaluateHOLFiniteState_seq_line780,checked] at run
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    have same := normal rfl
    subst middle
    dsimp only at run
    have globals := evaluate_readOnly_globals (.return (.var .local (ofString "it"))) (by decide) state
    rw [run] at globals
    exact globals

#print axioms rlpDecodeFully_continuation_returned_globals
end InitECandidate.Runtime
