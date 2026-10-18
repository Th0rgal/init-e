import InitECandidate.Runtime.TxListItemInputAbove
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem txListItem_input_returned_heap_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_list_item) = (some (.returned value),post))
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (fits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64) (above : ceiling ≤ outerArray.toNat) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_tx_list_item)
  rw [run] at metadata
  apply outerValid.after_memory_above state post outerArray outerCount outerInput outerLength fits metadata.2.1
  intro address aboveArray
  exact txListItem_input_returned_above state post array index input inputLength scratch frame filled ceiling inputLimit
    arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
    arena budget value run address (by omega)

#print axioms txListItem_input_returned_heap_independent_outer_prefix
end InitECandidate.Runtime
