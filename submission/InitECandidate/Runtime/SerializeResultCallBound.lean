import InitECandidate.Runtime.SerializeResultReturned
import InitECandidate.Runtime.OriginalSerializeResultCode
import InitECandidate.Runtime.PanFiveWordShapeLookup
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def serializeResultCallee (output root success chain schema : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((((HolFiniteMapExact.empty.update (ofString "out",.val (.word output))).update
    (ofString "root",.val (.word root))).update (ofString "succ",.val (.word success))).update
    (ofString "chain_id",.val (.word chain))).update (ofString "schema_id",.val (.word schema))

theorem serializeResult_callee_locals (output root success chain schema : BitVec 64) :
    (serializeResultCallee output root success chain schema).lookup (ofString "out") = some (.val (.word output)) ∧
    (serializeResultCallee output root success chain schema).lookup (ofString "root") = some (.val (.word root)) := by
  constructor <;> simp [serializeResultCallee,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "root" ≠ ofString "out" by decide,show ofString "succ" ≠ ofString "out" by decide,
    show ofString "chain_id" ≠ ofString "out" by decide,show ofString "schema_id" ≠ ofString "out" by decide,
    show ofString "succ" ≠ ofString "root" by decide,show ofString "chain_id" ≠ ofString "root" by decide,
    show ofString "schema_id" ≠ ofString "root" by decide]

theorem serializeResult_lookup {F : Type} (state : PanSemStateFiniteExact 64 F)
    (output root success chain schema : BitVec 64) (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "serialize_result")
      [.val (.word output),.val (.word root),.val (.word success),.val (.word chain),.val (.word schema)] =
      some (sourceFunctionBody Guest.guestFn_serialize_result,serializeResultCallee output root success chain schema,.one) := by
  exact pan_five_word_shape_lookup state.code.lookup (ofString "serialize_result")
    (ofString "out") (ofString "root") (ofString "succ") (ofString "chain_id") (ofString "schema_id")
    (sourceFunctionBody Guest.guestFn_serialize_result) .one output root success chain schema
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_serializeResult_lookup)

/-- The complete result serializer call, including entry and failed memory
accesses, uses at most 20 source clocks. -/
theorem evaluate_serializeResult_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (output root success chain schema : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word output),.val (.word root),.val (.word success),.val (.word chain),.val (.word schema)])
    (code : state.code = originalRuntimeCode) (budget : 20 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "serialize_result") arguments)
    state.clock ≤ evaluated.2.clock + 20 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := serializeResultCallee output root success chain schema
  let entry := callEntryStateHOLFinite state callee
  have locals := serializeResult_callee_locals output root success chain schema
  have bounded := evaluate_serializeResult_body_bounded entry output root locals.1 locals.2 code
    (by change 19 ≤ state.clock - 1; omega)
  have lookup := serializeResult_lookup state output root success chain schema code
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_serialize_result) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have evaluated := evaluate_call_body_clock_no_timeout state post (ofString "serialize_result") destination arguments _
      (sourceFunctionBody Guest.guestFn_serialize_result) callee .one result args lookup (by omega) bodyRun bounded.2.2
    dsimp only
    rw [evaluated.2]
    have spent : state.clock - 1 ≤ post.clock + 19 := bounded.1
    have kept : post.clock ≤ state.clock - 1 := bounded.2.1
    exact ⟨by omega,by omega,evaluated.1⟩

/-- The real serializer declaration resumes its caller with the exact
length 43, preserving the caller locals needed for the output-write bound. -/
theorem evaluate_serializeResult_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (tailCost : Nat) (arguments : List (ExpHOL 64))
    (output root success chain schema : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word output),.val (.word root),.val (.word success),.val (.word chain),.val (.word schema)])
    (code : state.code = originalRuntimeCode) (budget : 20 + tailCost ≤ state.clock)
    (tailBound : ∀ ready : PanSemStateFiniteExact 64 F,
      ready.locals = state.locals.update (name,.val (.word 43)) → ready.code = state.code →
      ready.memaddrs = state.memaddrs → tailCost ≤ ready.clock →
      let evaluated := evaluateHOLFiniteState ready continuation
      ready.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ ready.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name .one (ofString "serialize_result") arguments continuation)
    state.clock ≤ evaluated.2.clock + (20 + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := serializeResultCallee output root success chain schema
  let entry := callEntryStateHOLFinite state callee
  have locals := serializeResult_callee_locals output root success chain schema
  have bounded := evaluate_serializeResult_body_bounded entry output root locals.1 locals.2 code
    (by change 19 ≤ state.clock - 1; omega)
  have lookup := serializeResult_lookup state output root success chain schema code
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_serialize_result)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_serialize_result) with
  | mk result post =>
    rw [bodyRun] at bounded metadata
    dsimp only at bounded metadata
    have consumed : state.clock ≤ post.clock + 20 := by
      have spent : state.clock - 1 ≤ post.clock + 19 := bounded.1
      omega
    apply evaluate_decCall_continuation_bounded state post name (ofString "serialize_result") .one .one arguments
      [.val (.word output),.val (.word root),.val (.word success),.val (.word chain),.val (.word schema)]
      (sourceFunctionBody Guest.guestFn_serialize_result) continuation callee result 20 tailCost args lookup (by omega)
      bodyRun bounded.2.1 consumed bounded.2.2
    intro value returned
    have exactValue := serializeResult_returned_value entry post value (by rw [bodyRun,returned])
    subst value
    let ready := setVarHOLFinite name (.val (.word 43)) {post with locals := state.locals}
    exact tailBound ready rfl metadata.1 metadata.2.1 (by change tailCost ≤ post.clock; omega)

#print axioms evaluate_serializeResult_call_bounded
#print axioms evaluate_serializeResult_continuation_bounded
end InitECandidate.Runtime
