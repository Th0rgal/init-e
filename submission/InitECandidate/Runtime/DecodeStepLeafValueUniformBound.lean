import InitECandidate.Runtime.DecodeStepLeafValueCheck
import InitECandidate.Runtime.DecodeStepLeafUniformBound
import InitECandidate.Runtime.DecodeStepExtensionUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual conditional MPT failure guard is bounded for arbitrary conditions,
including expression failures; no path-local well-formedness is assumed. -/
theorem mpt_fail_guard_uniform_bounded (condition : ExpHOL 64) (failure : BitVec 64) :
    ProgBounded (.ite condition (.call (some (none,none)) (ofString "mpt_fail") [.const failure]) .skip) 1 := by
  have fail : ProgBounded (.call (some (none,none)) (ofString "mpt_fail") [.const failure]) 1 := by
    intro F s code budget
    have bound := evaluate_mptFail_call_bounded s (.const failure) failure code (by omega)
      (by rw [evalListHOLFinite_eq_toExact]; rfl)
    exact ⟨by rw [bound.1]; omega,by rw [bound.1]; omega,bound.2.1⟩
  have skipped : ProgBounded (.skip : ProgHOL 64) 0 := ProgBounded.straight .skip rfl
  intro F s code budget
  exact (ProgBounded.ite condition fail (ProgBounded.weaken skipped (by omega))) s code budget

/-- The original leaf-value type guard and actual leaf construction, including
rejection and failed stores, need no heap reserve or local-type assumptions. -/
theorem decode_step_leaf_value_uniform_bounded : ProgBounded decodeStepLeafValueContinuation 4 := by
  intro F s code budget
  rw [source_decodeStep_leaf_value_continuation]
  exact (ProgBounded.seq (mpt_fail_guard_uniform_bounded _ 6)
    decode_step_leaf_construction_uniform_bounded) s code budget

#print axioms mpt_fail_guard_uniform_bounded
#print axioms decode_step_leaf_value_uniform_bounded
end InitECandidate.Runtime
