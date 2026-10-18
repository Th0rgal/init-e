import InitECandidate.Runtime.SecpInitSource
import InitECandidate.Runtime.AllocationFragmentBound
import InitECandidate.Runtime.ByteStraightCalleeCallBound
import InitECandidate.Runtime.PanUniformCalleeCallBound
import InitECandidate.Runtime.PanSequenceCodeBound
import InitECandidate.Runtime.LookupCodeInstalledBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every call of secp_accel_init_block costs at most its entry tick, for all
argument values, inaccessible stores and shape failures. -/
theorem evaluate_secpAccelInitBlock_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 1 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "secp_accel_init_block") arguments)
    state.clock ≤ result.2.clock + 1 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_byteStraightCallee_call_bounded state _ destination arguments _ budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "secp_accel_init_block") _
    (sourceFunctionBody Guest.guestFn_secp_accel_init_block) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_secpAccelInitBlock_lookup) found
  rw [same,source_secpAccelInitBlock_body]
  decide

#print axioms evaluate_secpAccelInitBlock_call_bounded

/-- Every evaluation of the original secp256k1_init body costs at most four
ticks: already initialized, malformed scratch or heap globals, allocation
failure, inaccessible accelerator blocks and the successful first init. -/
theorem evaluate_secp256k1Init_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 4 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_secp256k1_init)
    state.clock ≤ result.2.clock + 4 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  rw [source_secp256k1Init_body]
  have guard := (AllocationFragment.conditional
    (.cmp .notEqual (.var .global (ofString "secp_accel_scratch")) (.const 0))
    (AllocationFragment.straight (.return (.const 0)) (by decide))
    (AllocationFragment.straight .skip (by decide))).bounded state code (by simp [AllocationFragment.cost])
  apply evaluate_sequence_code_bounded state _ _ 0 4 guard _ (by omega)
  intro next nextCode nextBudget
  have c1 := nextCode.trans code
  apply evaluate_sequence_code_bounded next _ _ 2 2
    (evaluate_alloc_uniform_call_bounded next _ _ c1 (by omega)) _ nextBudget
  intro n2 n2Code n2Budget
  have c2 := n2Code.trans c1
  apply evaluate_sequence_code_bounded n2 _ _ 1 1
    (evaluate_secpAccelInitBlock_call_bounded n2 _ _ c2 (by omega)) _ n2Budget
  intro n3 n3Code n3Budget
  have c3 := n3Code.trans c2
  apply evaluate_sequence_code_bounded n3 _ _ 1 0
    (evaluate_secpAccelInitBlock_call_bounded n3 _ _ c3 (by omega)) _ n3Budget
  intro n4 n4Code _
  exact (AllocationFragment.straight (.return (.const 0)) (by decide)).bounded n4 (n4Code.trans c3) (by simp [AllocationFragment.cost])

#print axioms evaluate_secp256k1Init_body_bounded

/-- The actual call `secp256k1_init()` costs at most five ticks in every outcome. -/
theorem evaluate_secp256k1Init_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 5 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "secp256k1_init") arguments)
    state.clock ≤ result.2.clock + 5 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "secp256k1_init") destination arguments 4 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "secp256k1_init") []
    (sourceFunctionBody Guest.guestFn_secp256k1_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_secp256k1Init_lookup) found
  rw [same]
  exact evaluate_secp256k1Init_body_bounded (callEntryStateHOLFinite state locals) code
    (by change 4 ≤ state.clock - 1; omega)

#print axioms evaluate_secp256k1Init_call_bounded
end InitECandidate.Runtime
