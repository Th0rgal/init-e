import InitECandidate.Runtime.TxListItemInputRange
import InitECandidate.Runtime.BlobHashesCostMonotone
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem txListItem_input_returned_blob_cost {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength : BitVec 64) (filled : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat + 9 < 2^64)
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_list_item) = (some (.returned value),post)) :
    ∃ pointer length : BitVec 64, value = .rStruct [.val (.word pointer),.val (.word length)] ∧
      input.toNat ≤ pointer.toNat ∧ pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat ∧
      pointer.toNat + length.toNat < 2^64 ∧ length.toNat ≤ inputLength.toNat ∧ blobHashesBodyCost length.toNat ≤ blobHashesBodyCost inputLength.toNat := by
  obtain ⟨pointer,length,shape,starts,ends,noWrap,bounded⟩ := txListItem_input_returned_range state post array index input inputLength
    filled arrayLocal indexLocal valid inside inputBound code ticks value run
  exact ⟨pointer,length,shape,starts,ends,noWrap,bounded,blobHashesBodyCost_mono bounded⟩

#print axioms txListItem_input_returned_blob_cost
end InitECandidate.Runtime
