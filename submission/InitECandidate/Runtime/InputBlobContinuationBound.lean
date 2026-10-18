import InitECandidate.Runtime.InputBlobBodyBound
import InitECandidate.Runtime.InputBlobReturned
import InitECandidate.Runtime.OriginalInputBlobCode
import InitECandidate.Runtime.PanNoArgsShapeLookup
import InitECandidate.Runtime.PanDecCallContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact geometry and caller bindings delivered by a successful input read. -/
def InputBlobReady {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer : BitVec 64) (ready : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ length : BitVec 64, length.toNat ≤ 134217712 ∧
    ready.locals = state.locals.update (name,.rStruct [.val (.word pointer),.val (.word length)]) ∧
    ready.globals = (setGlobalHOLFinite (ofString "heap_ptr")
      (.val (.word (allocationEnd pointer (length + 8)))) state).globals ∧
    (allocationEnd pointer (length + 8)).toNat ≤ 33806089496 ∧
    pointer.toNat + length.toNat + 8 ≤ (allocationEnd pointer (length + 8)).toNat ∧
    (allocationEnd pointer (length + 8)).toNat % 8 = 0 ∧
    ready.code = state.code ∧ ready.memaddrs = state.memaddrs

/-- Compose the original declared input call with a bound on its actual
continuation states. Oversized inputs and all early failures are included. -/
theorem evaluate_inputBlob_declaration_continuation_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name : MlS) (pointer : BitVec 64)
    (continuation : ProgHOL 64) (tailCost : Nat)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (heapBound : pointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : inputBlobBodyCost + 1 + tailCost ≤ state.clock)
    (tails : ∀ ready : PanSemStateFiniteExact 64 F, InputBlobReady state name pointer ready →
      tailCost ≤ ready.clock →
      let evaluated := evaluateHOLFiniteState ready continuation
      ready.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ ready.clock ∧
        evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state
      (.decCall name (.comb [.one,.one]) (ofString "input_blob") [] continuation)
    state.clock ≤ evaluated.2.clock + (inputBlobBodyCost + 1 + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have bounded := evaluate_inputBlob_body_bounded entry pointer heap heapBound code
    (by change inputBlobBodyCost ≤ state.clock - 1; omega)
  have lookup := pan_no_args_shape_lookup state.code.lookup (ofString "input_blob")
    (sourceFunctionBody Guest.guestFn_input_blob) (.comb [.one,.one])
    (by rw [code]; exact originalRuntimeCode_inputBlob_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_input_blob) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    obtain ⟨spent,remaining,noTimeout⟩ := bounded
    apply evaluate_decCall_continuation_bounded state post name (ofString "input_blob")
      (.comb [.one,.one]) (.comb [.one,.one]) [] []
      (sourceFunctionBody Guest.guestFn_input_blob) continuation HolFiniteMapExact.empty result
      (inputBlobBodyCost + 1) tailCost rfl lookup (by omega) bodyRun remaining
      (by change state.clock - 1 ≤ post.clock + inputBlobBodyCost at spent; omega) noTimeout
    intro value returned
    have actual : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_input_blob) =
        (some (.returned value),post) := bodyRun.trans (by rw [returned])
    obtain ⟨length,small,returnedValue,globals,capped,covers,aligned,domain,installed⟩ :=
      inputBlob_body_returned entry post pointer value heap heapBound code actual
    apply tails
    · refine ⟨length,small,?_,globals,capped,covers,aligned,installed,domain⟩
      simp only [setVarHOLFinite,returnedValue]
    · change state.clock - 1 ≤ post.clock + inputBlobBodyCost at spent
      change tailCost ≤ post.clock
      omega

#print axioms evaluate_inputBlob_declaration_continuation_bounded
end InitECandidate.Runtime
