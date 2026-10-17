import InitECandidate.Runtime.RlpErrorChecks
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpDecodeFullyContinuation : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_decode_fully with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem source_rlpDecodeFully_body : sourceFunctionBody Guest.guestFn_rlp_decode_fully =
    .decCall (ofString "it") (.comb [.one,.one,.one,.one]) (ofString "rlp_item")
      [.var .local (ofString "p"),.var .local (ofString "len")] rlpDecodeFullyContinuation := by
  simp only [rlpDecodeFullyContinuation,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpDecodeFully_continuation : rlpDecodeFullyContinuation =
    .seq (.ite (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len")))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 6]) .skip)
      (.return (.var .local (ofString "it"))) := by
  simp only [rlpDecodeFullyContinuation,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual full-decode check costs at most one tick, even when its
item or length locals are malformed. -/
theorem evaluate_rlpDecodeFully_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpDecodeFullyContinuation
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,normal,_⟩ := evaluate_rlp_error_check state
    (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len"))) 6 code ticks
  rw [source_rlpDecodeFully_continuation]
  apply evaluate_sequence_straight_bounded state _ _ 1
  · rw [run]
    exact ⟨cost,remaining,noTimeout⟩
  · decide

theorem evaluate_rlpDecodeFully_continuation_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpDecodeFullyContinuation).1 ≠ none := by
  rw [source_rlpDecodeFully_continuation]
  apply evaluate_seq_terminal
  intro current
  exact evaluate_return_terminal current _

#print axioms evaluate_rlpDecodeFully_continuation_bounded
#print axioms evaluate_rlpDecodeFully_continuation_terminal
end InitECandidate.Runtime
