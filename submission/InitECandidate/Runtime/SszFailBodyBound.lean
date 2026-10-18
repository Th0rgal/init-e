import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.TrapBodyClock
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sszFailBody : ProgHOL 64 :=
  .seq (.raise (ofString "SszErr") (.var .local (ofString "code"))) (.return (.const 0))

theorem source_ssz_fail_body : sourceFunctionBody Guest.guestFn_ssz_fail = sszFailBody := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- SSZ rejection consumes no body ticks and is terminal, including malformed
exception bindings. Function-call entry is charged separately. -/
theorem evaluate_ssz_fail_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ssz_fail)
    evaluated.2.clock = state.clock ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  rw [source_ssz_fail_body]
  have clock := clockPreserving_of_straightLine sszFailBody (by rfl) state
  have timeout := evaluate_straightLine_no_timeout sszFailBody (by rfl) state
  refine ⟨clock,timeout,?_⟩
  unfold sszFailBody
  rw [evaluateHOLFiniteState_seq_line780]
  have terminal := evaluate_raise_terminal state (ofString "SszErr") (.var .local (ofString "code"))
  cases ran : evaluateHOLFiniteState state (.raise (ofString "SszErr") (.var .local (ofString "code"))) with
  | mk result post =>
    rw [ran] at terminal
    cases result with
    | none => exact False.elim (terminal rfl)
    | some result => simp

#print axioms source_ssz_fail_body
#print axioms evaluate_ssz_fail_body_bounded
end InitECandidate.Runtime
