import InitECandidate.Runtime.InputBlobBodyBound
import InitECandidate.Runtime.OriginalInputBlobCode
import InitECandidate.Runtime.LookupCodeInstalledBody
import InitECandidate.Runtime.PanUniformCalleeCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual input_blob call, including entry, uses at most 16,777,218
source clocks for every declared input size. -/
theorem evaluate_inputBlob_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (heapPointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : inputBlobBodyCost + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "input_blob") [])
    state.clock ≤ evaluated.2.clock + (inputBlobBodyCost + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "input_blob") destination [] inputBlobBodyCost budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "input_blob") []
    (sourceFunctionBody Guest.guestFn_input_blob) body (.comb [.one,.one]) returnShape values locals
    (by rw [code]; exact originalRuntimeCode_inputBlob_lookup) found
  rw [same]
  exact evaluate_inputBlob_body_bounded (callEntryStateHOLFinite state locals) heapPointer heap heapBound code
    (by change inputBlobBodyCost ≤ state.clock - 1; omega)

#print axioms evaluate_inputBlob_call_bounded
end InitECandidate.Runtime
