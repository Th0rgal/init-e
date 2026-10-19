import InitECandidate.Runtime.HeaderRlpFieldInputBound
import InitECandidate.Runtime.OriginalHeaderRlpFieldCode
import InitECandidate.Runtime.PanThreeValueLookupShape
import InitECandidate.Runtime.PanTwoWordLookupShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def headerRlpFieldName : HeaderRlpField → MlS
  | .uint => ofString "hdr_uint_field"
  | .bytes => ofString "hdr_bytes_field"
  | .raw => ofString "hdr_raw_field"
def headerRlpFieldShape : HeaderRlpField → ShapeHOL
  | .bytes => .one
  | _ => .comb [.one,.one]
def headerRlpFieldValues (field : HeaderRlpField) (array index extra : BitVec 64) : List (ValueHOL 64) :=
  match field with
  | .raw => [.val (.word array),.val (.word index)]
  | _ => [.val (.word array),.val (.word index),.val (.word extra)]
def headerRlpFieldCallee (field : HeaderRlpField) (array index extra : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  let base := (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  match field with
  | .uint => base.update (ofString "maxb",.val (.word extra))
  | .bytes => base.update (ofString "width",.val (.word extra))
  | .raw => base

theorem header_rlp_field_lookup (field : HeaderRlpField) (array index extra : BitVec 64) :
    lookupCodeHOLFinite originalRuntimeCode.lookup (headerRlpFieldName field) (headerRlpFieldValues field array index extra) =
      some (sourceFunctionBody (headerRlpFieldDeclaration field),headerRlpFieldCallee field array index extra,headerRlpFieldShape field) := by
  cases field with
  | uint =>
    exact pan_three_value_lookup_shape _ _ _ _ _ _ _ (.word array) (.word index) (.word extra)
      (by decide) (by decide) (by decide) originalRuntimeCode_hdrUintField_lookup
  | bytes =>
    exact pan_three_value_lookup_shape _ _ _ _ _ _ _ (.word array) (.word index) (.word extra)
      (by decide) (by decide) (by decide) originalRuntimeCode_hdrBytesField_lookup
  | raw =>
    exact pan_two_word_lookup_shape _ _ _ _ _ _ array index (by decide) originalRuntimeCode_hdrRawField_lookup

/-- Installed original header-field calls consume actual slice entries and
spend the uniform parser bound plus the one call-entry tick, in every outcome. -/
theorem runBounded_header_rlp_field_call {F : Type} (s : PanSemStateFiniteExact 64 F) (field : HeaderRlpField)
    (array index extra pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some (headerRlpFieldValues field array index extra))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 1 ≤ s.clock) :
    RunBounded s (.call (some (destination,none)) (headerRlpFieldName field) arguments) (headerRlpFieldCost inputLimit + 1) := by
  apply RunBounded.call args budget
  intro body callee shape lookup
  rw [code,header_rlp_field_lookup field array index extra] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj lookup
  let callState := callEntryStateHOLFinite s (headerRlpFieldCallee field array index extra)
  have atArray : callState.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerRlpFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have atIndex : callState.locals.lookup (ofString "i") = some (.val (.word index)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerRlpFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have calleeEntry : RlpSliceInputEntry callState array index pointer length input inputLength :=
    entry.after_frame s callState _ _ _ _ _ _ rfl rfl rfl
  exact runBounded_header_rlp_field_input callState field array index pointer length input inputLength scratch frame
    ceiling inputLimit atArray atIndex calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena (by change headerRlpFieldCost inputLimit ≤ s.clock - 1; omega)

#print axioms header_rlp_field_lookup
#print axioms runBounded_header_rlp_field_call
end InitECandidate.Runtime
