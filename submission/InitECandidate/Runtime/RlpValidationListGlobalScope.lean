import InitECandidate.Runtime.RlpValidationListContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Normal completion of the original list continuation executes its actual
list push with computed payload/after locals; scope restoration preserves the
push clock and memory results. -/
theorem evaluate_rlpValidation_list_continuation_globals_scope {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position header payload : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (headerLocal : state.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]))
    (run : evaluateHOLFiniteState state rlpValidationHeaderContinuation = (none,post)) :
    ∃ output, evaluateHOLFiniteState (rlpValidationListEntry state position header payload) rlpValidationListPush = (none,output) ∧
      post.globals = output.globals := by
  have initial := eval_rlp_validator_payload state position header payload 1 positionLocal headerLocal
  rw [source_rlpValidation_header_continuation] at run
  obtain ⟨out1,run1,restore1⟩ := evaluate_dec_word_result_scope state post (ofString "payload")
    (.op .add [.var .local (ofString "pos"),.rfield 0 (.var .local (ofString "h"))]) (position + header) _ none initial run
  let first := setVarHOLFinite (ofString "payload") (.val (.word (position + header))) state
  have atHeader : first.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]) := by
    simpa [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "payload" ≠ ofString "h" by decide] using headerLocal
  have atPayload : first.locals.lookup (ofString "payload") = some (.val (.word (position + header))) := by
    simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have next := eval_rlp_validator_after first position header payload 1 atPayload atHeader
  obtain ⟨output,run2,restore2⟩ := evaluate_dec_word_result_scope first out1 (ofString "after")
    (.op .add [.var .local (ofString "payload"),.rfield 1 (.var .local (ofString "h"))])
    (position + header + payload) rlpValidationAfterHeader none next run1
  let entered := rlpValidationListEntry state position header payload
  have headerEntered : entered.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]) := by
    simpa [entered,rlpValidationListEntry,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "payload" ≠ ofString "h" by decide,show ofString "after" ≠ ofString "h" by decide] using headerLocal
  have actual : evaluateHOLFiniteState entered rlpValidationListPush = (none,output) := by
    change evaluateHOLFiniteState entered rlpValidationAfterHeader = (none,output) at run2
    rw [source_rlpValidation_after_header,evaluateHOLFiniteState_ite] at run2
    have guard : @evalHOLExact 64 F _ entered.toExact
        (fun address => Classical.propDecidable (entered.memaddrs address))
        (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerEntered,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard] at run2
    simpa only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] using run2
  refine ⟨output,actual,?_⟩
  rw [restore1,restore2]

#print axioms evaluate_rlpValidation_list_continuation_globals_scope
end InitECandidate.Runtime
