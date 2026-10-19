import InitECandidate.Runtime.HeaderNumericFieldCallBound
import InitECandidate.Runtime.HeaderWordReturnedFrame
import InitECandidate.Runtime.HeaderU256ReturnedFrame
import InitECandidate.Runtime.PanLocalCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The decoder's original numeric-field assignment calls retain the actual
slice table and globals while binding their checked word or four-word result. -/
theorem header_numeric_field_call_normal_frame {F : Type} (s post : PanSemStateFiniteExact 64 F) (field : HeaderNumericField)
    (array index extra pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some (headerNumericFieldValues field array index extra))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock)
    (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (headerNumericFieldName field) arguments) = (none,post)) :
    ∃ value : ValueHOL 64, post.locals = s.locals.update (name,value) ∧
      shapeEqHOL (shapeOfHOLExact value) (headerNumericFieldShape field) = true ∧
      post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (∀ global : MlS, post.globals.lookup global = s.globals.lookup global) ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → post.memory address = s.memory address) := by
  have lookup := header_numeric_field_lookup field array index extra
  rw [← code] at lookup
  obtain ⟨value,bodyPost,bodyRun,checked,resumed⟩ := evaluate_localCall_normal_result s post name
    (headerNumericFieldName field) (headerNumericFieldShape field) arguments (headerNumericFieldValues field array index extra)
    (sourceFunctionBody (headerNumericFieldDeclaration field)) (headerNumericFieldCallee field array index extra) args lookup run
  let callState := callEntryStateHOLFinite s (headerNumericFieldCallee field array index extra)
  have atArray : callState.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerNumericFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have atIndex : callState.locals.lookup (ofString "i") = some (.val (.word index)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerNumericFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have calleeEntry : RlpSliceInputEntry callState array index pointer length input inputLength :=
    entry.after_frame s callState _ _ _ _ _ _ rfl rfl rfl
  have parserBound : headerRlpFieldCost inputLimit + 1 ≤ callState.clock := by
    change headerRlpFieldCost inputLimit + 1 ≤ s.clock - 1
    omega
  have bodyFrame : bodyPost.memaddrs = callState.memaddrs ∧ bodyPost.code = callState.code ∧
      (∀ global : MlS, bodyPost.globals.lookup global = callState.globals.lookup global) ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → bodyPost.memory address = callState.memory address) := by
    cases field with
    | word =>
      exact header_word_body_returned_frame callState bodyPost array index pointer length input inputLength scratch frame
        ceiling inputLimit atArray atIndex calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
        framePositive scratchBelow arena parserBound value bodyRun
    | u256 =>
      have atMaxb : callState.locals.lookup (ofString "maxb") = some (.val (.word extra)) := by
        simp [callState,callEntryStateHOLFinite,headerNumericFieldCallee,HolFiniteMapExact.lookup_update,FUPDATE]
      exact header_u256_body_returned_frame callState bodyPost array index extra pointer length input inputLength scratch frame
        ceiling inputLimit atArray atIndex atMaxb calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
        framePositive scratchBelow arena parserBound value bodyRun
  obtain ⟨domain,installed,globals,memory⟩ := bodyFrame
  refine ⟨value,?_,checked,?_,?_,?_,?_⟩
  · rw [resumed]; rfl
  · rw [resumed]; exact domain
  · rw [resumed]; exact installed
  · intro global; rw [resumed]; exact globals global
  · intro address above; rw [resumed]; exact memory address above

#print axioms header_numeric_field_call_normal_frame
end InitECandidate.Runtime
