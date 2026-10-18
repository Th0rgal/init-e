import InitECandidate.Runtime.RlpDecodeFullyContinuation
import InitECandidate.Runtime.RlpErrorCheckFlow
import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successfully returned full-decode check leaves the entire memory
unchanged, without a local-shape or clock premise. -/
theorem rlpDecodeFully_continuation_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpDecodeFullyContinuation = (some (.returned value),post)) :
    post.memory = state.memory := by
  obtain ⟨result,middle,checked,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
    (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len"))) 6 code
  rw [source_rlpDecodeFully_continuation,evaluateHOLFiniteState_seq_line780,checked] at run
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    have same := normal rfl
    subst middle
    dsimp only at run
    have memory := evaluate_readOnly_memory (.return (.var .local (ofString "it"))) (by decide) state
    rw [run] at memory
    exact memory

#print axioms rlpDecodeFully_continuation_returned_memory
end InitECandidate.Runtime
