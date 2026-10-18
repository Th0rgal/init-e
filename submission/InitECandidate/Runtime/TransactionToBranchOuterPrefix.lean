import InitECandidate.Runtime.TransactionToSource
import InitECandidate.Runtime.TxToItemLocalCallOuterPrefix
import InitECandidate.Runtime.TxFixedBytesLocalCallOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_to_branch_normal_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (run : evaluateHOLFiniteState state transactionToBranch = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  have fixedArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "k"),.const 20] =
      some [.val (.word array),.val (.word index),.val (.word (20 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have optionalArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "k")] = some [.val (.word array),.val (.word index)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  unfold transactionToBranch at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · exact txToItem_local_call_outer_prefix state post (ofString "w") _ array index input inputLength scratch frame count ceiling inputLimit
        optionalArgs valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget outerArray outerCount outerInput outerLength outerValid outerBelow run
    · exact txFixedBytes_local_call_outer_prefix state post (ofString "w") _ array index 20 input inputLength scratch frame count ceiling inputLimit
        fixedArgs valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget outerArray outerCount outerInput outerLength outerValid outerBelow run
  · cases run

#print axioms transaction_to_branch_normal_outer_prefix
end InitECandidate.Runtime
