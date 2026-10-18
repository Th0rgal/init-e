import InitECandidate.Runtime.RlpSliceInputArguments
import InitECandidate.Runtime.TxScalarWordBodyBelow
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful field extraction preserves any earlier outer slice prefix
below the scratch frame, even when it reads a distinct inner slice array. -/
theorem txScalarWord_input_returned_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index maximum input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (maxLocal : state.locals.lookup (ofString "maxb") = some (.val (.word maximum)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92642 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_scalar_word) = (some (.returned value),post))
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  let entry := callEntryStateHOLFinite state (txScalarWordCallee array index maximum)
  have arr : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have idx : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "i" by decide]
  have retained : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  obtain ⟨pointer,length,args,noWrap,lengthBound,_,_⟩ := rlpSliceInputPrefix_fixed_bytes_arguments entry
    array index input inputLength count.toNat arr idx retained inside
  have factor : (2 * length.toNat + 1) * 15 + 19 ≤ (2 * inputLength.toNat + 1) * 15 + 19 := by omega
  have cost := Nat.mul_le_mul lengthBound factor
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_tx_scalar_word)
  rw [run] at metadata
  apply RlpSliceInputPrefix.after_memory_below state post outerArray outerCount outerInput outerLength frame outerValid outerBelow metadata.2.1
  intro address below
  exact txScalarWord_body_returned_below state post array index maximum pointer length scratch frame ceiling inputLimit
    arrayLocal indexLocal maxLocal args noWrap (by omega) limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena (by omega) value run address below

#print axioms txScalarWord_input_returned_independent_outer_prefix
end InitECandidate.Runtime
