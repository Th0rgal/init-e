import InitECandidate.Runtime.TxListItemBodyRange
import InitECandidate.Runtime.RlpSliceInputArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful nested list extraction returns a nonwrapping subinterval of
the original whole input, and its length is bounded by the whole-input length. -/
theorem txListItem_input_returned_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength : BitVec 64) (filled : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat + 9 < 2^64)
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_list_item) = (some (.returned value),post)) :
    ∃ pointer length : BitVec 64, value = .rStruct [.val (.word pointer),.val (.word length)] ∧
      input.toNat ≤ pointer.toNat ∧ pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat ∧
      pointer.toNat + length.toNat < 2^64 ∧ length.toNat ≤ inputLength.toNat := by
  obtain ⟨itemPointer,itemLength,args,noWrap,lengthBound,startsWithin,endsWithin⟩ := rlpSliceInputPrefix_fixed_bytes_arguments
    state array index input inputLength filled arrayLocal indexLocal valid inside
  obtain ⟨pointer,length,shape,starts,ends,bounded⟩ := txListItem_body_returned_range state post itemPointer itemLength
    args noWrap (by omega) code ticks value run
  exact ⟨pointer,length,shape,Nat.le_trans startsWithin starts,Nat.le_trans ends endsWithin,bounded,by omega⟩

#print axioms txListItem_input_returned_range
end InitECandidate.Runtime
