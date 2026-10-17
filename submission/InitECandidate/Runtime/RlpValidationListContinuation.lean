import InitECandidate.Runtime.RlpValidationPushNormal
import InitECandidate.Runtime.RlpValidationHeaderGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def rlpValidationListEntry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "after") (.val (.word (position + header + payload)))
    (setVarHOLFinite (ofString "payload") (.val (.word (position + header))) state)

/-- Normal completion of the original list continuation executes its actual
list push with computed payload/after locals; scope restoration preserves the
push clock and memory results. -/
theorem evaluate_rlpValidation_list_continuation_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position header payload : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (headerLocal : state.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]))
    (run : evaluateHOLFiniteState state rlpValidationHeaderContinuation = (none,post)) :
    ∃ output, evaluateHOLFiniteState (rlpValidationListEntry state position header payload) rlpValidationListPush = (none,output) ∧
      post.clock = output.clock ∧ post.memory = output.memory ∧
      (∀ name, name ≠ ofString "payload" → name ≠ ofString "after" → post.locals.lookup name = output.locals.lookup name) := by
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
  refine ⟨output,actual,?_,?_,?_⟩
  · rw [restore1,restore2]
  · rw [restore1,restore2]
  · intro name notPayload notAfter
    rw [restore1,restore2]
    rw [restore_other_local _ _ name _ notPayload,restore_other_local _ _ name _ notAfter]

/-- A normally completed original list continuation enters its actual nested
interval and saves the parent fields, including allocator and local scopes. -/
theorem rlpValidation_list_continuation_post {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop top header payload scratch frame : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word top)))
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock) (orderedFrame : frame ≤ scratch)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (run : evaluateHOLFiniteState state rlpValidationHeaderContinuation = (none,post)) :
    post.clock = state.clock - 1 ∧
      post.locals.lookup (ofString "pos") = some (.val (.word (position + header))) ∧
      post.locals.lookup (ofString "end") = some (.val (.word (position + header + payload))) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (scratchAllocationEnd scratch 24))) ∧
      post.memory (scratchAllocationEnd scratch 24) = .word (position + header + payload) ∧
      post.memory (scratchAllocationEnd scratch 24 + 8) = .word stop ∧
      post.memory (scratchAllocationEnd scratch 24 + 16) = .word top := by
  obtain ⟨output,pushRun,clock,memory,locals⟩ := evaluate_rlpValidation_list_continuation_normal state post position header payload
    positionLocal headerLocal run
  let entered := rlpValidationListEntry state position header payload
  have localFrame : ∀ name, name ≠ ofString "payload" → name ≠ ofString "after" → entered.locals.lookup name = state.locals.lookup name := by
    intro name differentPayload differentAfter
    simp [entered,rlpValidationListEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm differentPayload,Ne.symm differentAfter]
  have atPayload : entered.locals.lookup (ofString "payload") = some (.val (.word (position + header))) := by
    simp [entered,rlpValidationListEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "after" ≠ ofString "payload" by decide]
  have atAfter : entered.locals.lookup (ofString "after") = some (.val (.word (position + header + payload))) := by
    simp [entered,rlpValidationListEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have fields := rlpValidation_list_push_normal_post entered output position stop top (position + header)
    (position + header + payload) scratch frame
    ((localFrame _ (by decide) (by decide)).trans positionLocal) ((localFrame _ (by decide) (by decide)).trans stopLocal)
    ((localFrame _ (by decide) (by decide)).trans topLocal) atPayload atAfter code ticks scratchGlobal frameGlobal orderedFrame arena pushRun
  refine ⟨clock.trans fields.1,?_,?_,?_,?_,?_,?_⟩
  · exact (locals _ (by decide) (by decide)).trans fields.2.1
  · exact (locals _ (by decide) (by decide)).trans fields.2.2.1
  · exact (locals _ (by decide) (by decide)).trans fields.2.2.2.1
  · rw [memory]; exact fields.2.2.2.2.1
  · rw [memory]; exact fields.2.2.2.2.2.1
  · rw [memory]; exact fields.2.2.2.2.2.2

#print axioms rlpValidation_list_continuation_post
#print axioms evaluate_rlpValidation_list_continuation_normal
end InitECandidate.Runtime
