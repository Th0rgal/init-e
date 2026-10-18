import InitECandidate.Runtime.OriginalBswap64Code
import InitECandidate.Runtime.LookupCodeInstalledBody
import InitECandidate.Runtime.StraightCalleeContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem bswap64_body_straight : straightLine (sourceFunctionBody Guest.guestFn_bswap64) = true := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The real byte swap adds one call clock to any bounded continuation;
invalid arguments or return shapes terminate within the same budget. -/
theorem evaluate_bswap64_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (tailCost : Nat) (code : state.code = originalRuntimeCode)
    (tail : ∀ current : PanSemStateFiniteExact 64 F, current.code = originalRuntimeCode → tailCost ≤ current.clock →
      let evaluated := evaluateHOLFiniteState current continuation
      current.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ current.clock ∧
        evaluated.1 ≠ some .timeOut)
    (budget : 1 + tailCost ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape (ofString "bswap64") arguments continuation)
    state.clock ≤ evaluated.2.clock + (1 + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  apply evaluate_straightCallee_continuation_bounded state name (ofString "bswap64") shape arguments continuation tailCost
  · intro values body locals returnShape found
    have installed : state.code.lookup (ofString "bswap64") =
        some ([(ofString "x",.one)],sourceFunctionBody Guest.guestFn_bswap64,.one) := by
      rw [code]; exact originalRuntimeCode_bswap64_lookup
    have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "bswap64")
      [(ofString "x",.one)] (sourceFunctionBody Guest.guestFn_bswap64) body .one returnShape values locals installed found
    rw [same]
    exact bswap64_body_straight
  · intro current same enough
    exact tail current (same.trans code) enough
  · exact budget

#print axioms evaluate_bswap64_call_bounded
end InitECandidate.Runtime
