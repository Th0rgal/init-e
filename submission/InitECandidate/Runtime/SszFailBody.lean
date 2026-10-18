import InitECandidate.Runtime.TrieWalkLeafTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_sszFail_body : sourceFunctionBody Guest.guestFn_ssz_fail =
    .seq (.raise (ofString "SszErr") (.var .local (ofString "code"))) (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem sszFail_straightLine : straightLine (sourceFunctionBody Guest.guestFn_ssz_fail) = true := by
  rw [source_sszFail_body]
  rfl

/-- The original error helper's literal return is unreachable: raising either
produces an exception or an error. -/
theorem evaluate_sszFail_body_no_return {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ssz_fail)).1 ≠ some (.returned value) := by
  have noReturn : (evaluateHOLFiniteState state (.raise (ofString "SszErr") (.var .local (ofString "code")))).1 ≠ some (.returned value) := by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  have terminal := evaluate_raise_terminal state (ofString "SszErr") (.var .local (ofString "code"))
  rw [source_sszFail_body,evaluateHOLFiniteState_seq_line780]
  cases raised : evaluateHOLFiniteState state (.raise (ofString "SszErr") (.var .local (ofString "code"))) with
  | mk result middle =>
    rw [raised] at noReturn terminal
    cases result with
    | none => exact False.elim (terminal rfl)
    | some result => exact noReturn

#print axioms source_sszFail_body
#print axioms sszFail_straightLine
#print axioms evaluate_sszFail_body_no_return
end InitECandidate.Runtime
