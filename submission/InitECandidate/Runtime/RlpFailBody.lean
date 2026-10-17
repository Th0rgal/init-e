import InitECandidate.Runtime.TrieWalkLeafTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpFail_body : sourceFunctionBody Guest.guestFn_rlp_fail =
    .seq (.raise (ofString "RlpErr") (.var .local (ofString "code"))) (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem rlpFail_straightLine : straightLine (sourceFunctionBody Guest.guestFn_rlp_fail) = true := by
  rw [source_rlpFail_body]
  rfl

/-- The original error helper's literal return is unreachable: raising either
produces an exception or an error. -/
theorem evaluate_rlpFail_body_no_return {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_fail)).1 ≠ some (.returned value) := by
  have noReturn : (evaluateHOLFiniteState state (.raise (ofString "RlpErr") (.var .local (ofString "code")))).1 ≠ some (.returned value) := by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  have terminal := evaluate_raise_terminal state (ofString "RlpErr") (.var .local (ofString "code"))
  rw [source_rlpFail_body,evaluateHOLFiniteState_seq_line780]
  cases raised : evaluateHOLFiniteState state (.raise (ofString "RlpErr") (.var .local (ofString "code"))) with
  | mk result middle =>
    rw [raised] at noReturn terminal
    cases result with
    | none => exact False.elim (terminal rfl)
    | some result => exact noReturn

#print axioms source_rlpFail_body
#print axioms rlpFail_straightLine
#print axioms evaluate_rlpFail_body_no_return
end InitECandidate.Runtime
