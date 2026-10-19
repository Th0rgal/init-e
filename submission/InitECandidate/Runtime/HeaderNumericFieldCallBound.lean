import InitECandidate.Runtime.HeaderWordBodyBound
import InitECandidate.Runtime.HeaderU256BodyBound
import InitECandidate.Runtime.OriginalHeaderNumericFieldCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive HeaderNumericField where
  | word | u256

def headerNumericFieldName : HeaderNumericField → MlS
  | .word => ofString "hdr_word_field"
  | .u256 => ofString "hdr_u256_field"
def headerNumericFieldDeclaration : HeaderNumericField → Decl (BitVec 64)
  | .word => Guest.guestFn_hdr_word_field
  | .u256 => Guest.guestFn_hdr_u256_field
def headerNumericFieldShape : HeaderNumericField → ShapeHOL
  | .word => .one
  | .u256 => .comb [.one,.one,.one,.one]
def headerNumericFieldValues (field : HeaderNumericField) (array index extra : BitVec 64) : List (ValueHOL 64) :=
  match field with
  | .word => [.val (.word array),.val (.word index)]
  | .u256 => [.val (.word array),.val (.word index),.val (.word extra)]
def headerNumericFieldCallee (field : HeaderNumericField) (array index extra : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  let base := (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  match field with
  | .word => base
  | .u256 => base.update (ofString "maxb",.val (.word extra))

theorem header_numeric_field_lookup (field : HeaderNumericField) (array index extra : BitVec 64) :
    lookupCodeHOLFinite originalRuntimeCode.lookup (headerNumericFieldName field) (headerNumericFieldValues field array index extra) =
      some (sourceFunctionBody (headerNumericFieldDeclaration field),headerNumericFieldCallee field array index extra,headerNumericFieldShape field) := by
  cases field with
  | word =>
    exact pan_two_word_lookup_shape _ _ _ _ _ _ array index (by decide) originalRuntimeCode_hdrWordField_lookup
  | u256 =>
    exact pan_three_value_lookup_shape _ _ _ _ _ _ _ (.word array) (.word index) (.word extra)
      (by decide) (by decide) (by decide) originalRuntimeCode_hdrU256Field_lookup

/-- Both original numeric header-field calls have a uniform input-quadratic
bound, including their parser, checked byte conversion and call-entry ticks. -/
theorem runBounded_header_numeric_field_call {F : Type} (s : PanSemStateFiniteExact 64 F) (field : HeaderNumericField)
    (array index extra pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some (headerNumericFieldValues field array index extra))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock) :
    RunBounded s (.call (some (destination,none)) (headerNumericFieldName field) arguments) (headerRlpFieldCost inputLimit + 35) := by
  apply RunBounded.call (bodyCost := headerRlpFieldCost inputLimit + 34) args (by omega)
  intro body callee shape lookup
  rw [code,header_numeric_field_lookup field array index extra] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj lookup
  let callState := callEntryStateHOLFinite s (headerNumericFieldCallee field array index extra)
  have atArray : callState.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerNumericFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have atIndex : callState.locals.lookup (ofString "i") = some (.val (.word index)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerNumericFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have calleeEntry : RlpSliceInputEntry callState array index pointer length input inputLength :=
    entry.after_frame s callState _ _ _ _ _ _ rfl rfl rfl
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

#print axioms header_numeric_field_lookup
#print axioms runBounded_header_numeric_field_call
end InitECandidate.Runtime
