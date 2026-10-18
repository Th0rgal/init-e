import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.OriginalSha256InitCode
import InitECandidate.Runtime.OriginalKeccakInitCode
import InitECandidate.Runtime.OriginalSszInitCode
import InitECandidate.Runtime.OriginalU256WsInitCode
import InitECandidate.Runtime.OriginalRipemd160InitCode
import InitECandidate.Runtime.OriginalBlake2InitCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original sha256_init call, including its entry tick. -/
theorem evaluate_sha256Init_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 7 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "sha256_init") arguments)
    state.clock ≤ result.2.clock + 7 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "sha256_init") destination arguments 6 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "sha256_init") []
    (sourceFunctionBody Guest.guestFn_sha256_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_sha256Init_lookup) found
  rw [same]
  exact evaluate_sha256Init_body_bounded (callEntryStateHOLFinite state locals) code
    (by change 6 ≤ state.clock - 1; omega)

#print axioms evaluate_sha256Init_call_bounded

/-- The actual original keccak_init call, including its entry tick. -/
theorem evaluate_keccakInit_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 5 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "keccak_init") arguments)
    state.clock ≤ result.2.clock + 5 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "keccak_init") destination arguments 4 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "keccak_init") []
    (sourceFunctionBody Guest.guestFn_keccak_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_keccakInit_lookup) found
  rw [same]
  exact evaluate_keccakInit_body_bounded (callEntryStateHOLFinite state locals) code
    (by change 4 ≤ state.clock - 1; omega)

#print axioms evaluate_keccakInit_call_bounded

/-- The actual original ssz_init call, including its entry tick. -/
theorem evaluate_sszInit_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 7 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "ssz_init") arguments)
    state.clock ≤ result.2.clock + 7 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "ssz_init") destination arguments 6 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "ssz_init") []
    (sourceFunctionBody Guest.guestFn_ssz_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_sszInit_lookup) found
  rw [same]
  exact evaluate_sszInit_body_bounded (callEntryStateHOLFinite state locals) code
    (by change 6 ≤ state.clock - 1; omega)

#print axioms evaluate_sszInit_call_bounded

/-- The actual original u256_ws_init call, including its entry tick. -/
theorem evaluate_u256WsInit_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 3 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "u256_ws_init") arguments)
    state.clock ≤ result.2.clock + 3 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "u256_ws_init") destination arguments 2 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "u256_ws_init") []
    (sourceFunctionBody Guest.guestFn_u256_ws_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_u256WsInit_lookup) found
  rw [same]
  exact evaluate_u256WsInit_body_bounded (callEntryStateHOLFinite state locals) code
    (by change 2 ≤ state.clock - 1; omega)

#print axioms evaluate_u256WsInit_call_bounded

/-- The actual original ripemd160_init call, including its entry tick. -/
theorem evaluate_ripemd160Init_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 9 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "ripemd160_init") arguments)
    state.clock ≤ result.2.clock + 9 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "ripemd160_init") destination arguments 8 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "ripemd160_init") []
    (sourceFunctionBody Guest.guestFn_ripemd160_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_ripemd160Init_lookup) found
  rw [same]
  exact evaluate_ripemd160Init_body_bounded (callEntryStateHOLFinite state locals) code
    (by change 8 ≤ state.clock - 1; omega)

#print axioms evaluate_ripemd160Init_call_bounded

/-- The actual original blake2_init call, including its entry tick. -/
theorem evaluate_blake2Init_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 7 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "blake2_init") arguments)
    state.clock ≤ result.2.clock + 7 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "blake2_init") destination arguments 6 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "blake2_init") []
    (sourceFunctionBody Guest.guestFn_blake2_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_blake2Init_lookup) found
  rw [same]
  exact evaluate_blake2Init_body_bounded (callEntryStateHOLFinite state locals) code
    (by change 6 ≤ state.clock - 1; omega)

#print axioms evaluate_blake2Init_call_bounded

end InitECandidate.Runtime
