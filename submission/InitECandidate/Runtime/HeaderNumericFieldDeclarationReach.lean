import InitECandidate.Runtime.HeaderNumericFieldDeclarationFrame
import InitECandidate.Runtime.BoundedDecCallReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- Actual numeric declarations reach the next source statement with checked
word/u256 output and retained workspace/high memory, or terminate within the bound. -/
theorem header_numeric_field_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (field : HeaderNumericField)
    (array index extra pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64)
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
 :
    Reaches s (.decCall name shape (headerNumericFieldName field) arguments continuation)
      (fun ready => ∃ value : ValueHOL 64,
        ready.locals = s.locals.update (name,value) ∧
        shapeEqHOL (shapeOfHOLExact value) shape = true ∧
        shapeEqHOL (shapeOfHOLExact value) (headerNumericFieldShape field) = true ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 35) continuation := by
  let callState := callEntryStateHOLFinite s (headerNumericFieldCallee field array index extra)
  have atArray : callState.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerNumericFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have atIndex : callState.locals.lookup (ofString "i") = some (.val (.word index)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerNumericFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have calleeEntry : RlpSliceInputEntry callState array index pointer length input inputLength :=
    entry.after_frame s callState _ _ _ _ _ _ rfl rfl rfl
  have bounded : RunBounded callState (sourceFunctionBody (headerNumericFieldDeclaration field))
      (headerRlpFieldCost inputLimit + 34) := by
      cases field with
      | word =>
        exact (runBounded_header_word_body callState array index pointer length input inputLength scratch frame
          ceiling inputLimit atArray atIndex calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
          framePositive scratchBelow arena (by change headerRlpFieldCost inputLimit + 9 ≤ s.clock - 1; omega)).weaken (by omega)
      | u256 =>
        have atMaxb : callState.locals.lookup (ofString "maxb") = some (.val (.word extra)) := by
          simp [callState,callEntryStateHOLFinite,headerNumericFieldCallee,HolFiniteMapExact.lookup_update,FUPDATE]
        exact runBounded_header_u256_body callState array index extra pointer length input inputLength scratch frame
          ceiling inputLimit atArray atIndex atMaxb calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
          framePositive scratchBelow arena (by change headerRlpFieldCost inputLimit + 34 ≤ s.clock - 1; omega)
    
  have lookup := header_numeric_field_lookup field array index extra
  rw [← code] at lookup
  apply bounded_decCall_reaches s name (headerNumericFieldName field) shape (headerNumericFieldShape field) arguments
    (headerNumericFieldValues field array index extra) (sourceFunctionBody (headerNumericFieldDeclaration field)) continuation
    (headerNumericFieldCallee field array index extra) (headerRlpFieldCost inputLimit + 34)
  · exact args
  · exact lookup
  · omega
  · exact bounded
  · intro value post returned checked
    have parserBound : headerRlpFieldCost inputLimit + 1 ≤ callState.clock := by
      change headerRlpFieldCost inputLimit + 1 ≤ s.clock - 1
      omega
    have bodyFrame : post.memaddrs = callState.memaddrs ∧ post.code = callState.code ∧
        (∀ global : MlS, post.globals.lookup global = callState.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → post.memory address = callState.memory address) := by
      cases field with
      | word =>
        exact header_word_body_returned_frame callState post array index pointer length input inputLength scratch frame
          ceiling inputLimit atArray atIndex calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
          framePositive scratchBelow arena parserBound value returned
      | u256 =>
        have atMaxb : callState.locals.lookup (ofString "maxb") = some (.val (.word extra)) := by
          simp [callState,callEntryStateHOLFinite,headerNumericFieldCallee,HolFiniteMapExact.lookup_update,FUPDATE]
        exact header_u256_body_returned_frame callState post array index extra pointer length input inputLength scratch frame
          ceiling inputLimit atArray atIndex atMaxb calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
          framePositive scratchBelow arena parserBound value returned
    obtain ⟨domain,installed,globals,memory⟩ := bodyFrame
    exact ⟨value,rfl,checked.1,checked.2,domain,installed,globals,memory⟩

#print axioms header_numeric_field_declaration_reaches
end InitECandidate.Runtime
