import InitECandidate.Runtime.TransactionDataFieldPrefix
import InitECandidate.Runtime.TransactionDataFieldOuterPrefix
import InitECandidate.Runtime.TransactionDataFieldGlobals
import InitECandidate.Runtime.TransactionDataFieldBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_data_field_normal_runtime_frame {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 200 < array.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state transactionDataField = (none,final)) :
    RlpSliceInputPrefix final array input inputLength count.toNat ∧
      RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      final.globals.lookup (ofString "heap_ptr") = state.globals.lookup (ofString "heap_ptr") ∧
      (∀ name, name ≠ ofString "k" → final.locals.lookup name = state.locals.lookup name) ∧
      final.locals.lookup (ofString "k") = some (.val (.word (index + 1))) ∧
      final.code = state.code ∧ final.memaddrs = state.memaddrs ∧
      state.clock ≤ final.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) ∧
      final.clock ≤ state.clock := by
  have slices := transaction_data_field_normal_prefix state final array count index tx input inputLength scratch frame ceiling inputLimit
    arrayLocal indexLocal txLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    arrayBeforeFrame headerBefore budget run
  have outer := transaction_data_field_normal_outer_prefix state final array count index tx input inputLength scratch frame ceiling inputLimit
    arrayLocal indexLocal txLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    outerArray outerCount outerInput outerLength outerValid outerBelow beforeTx (Nat.lt_trans headerBefore array.isLt) budget run
  have globals := transaction_data_field_normal_globals state final array count index input inputLength scratch frame ceiling inputLimit
    arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget run
  have bounded := evaluate_transaction_data_field_bounded state array count index input inputLength scratch frame ceiling inputLimit
    arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  have metadata := evaluateHOLFiniteState_metadata state transactionDataField
  rw [run] at bounded metadata
  exact ⟨slices,outer,globals.1,globals.2.1,globals.2.2,
    fun name different => transaction_data_field_other_local state final name different run,
    transactionDataField_increments state final index indexLocal run,metadata.1,metadata.2.1,bounded.1,bounded.2.1⟩

#print axioms transaction_data_field_normal_runtime_frame
end InitECandidate.Runtime
