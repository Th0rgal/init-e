import InitECandidate.Runtime.TransactionU256FieldHeapOuterFrame
import InitECandidate.Runtime.TransactionU256FieldBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_u256_field_normal_heap_runtime_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx offset : BitVec 64) (arguments : List (ExpHOL 64))
    (array index maximum input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word maximum)])
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + offset.toNat + 24 < array.toNat)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments)
        (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v")))) = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
      RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      (∀ other, other ≠ ofString "v" → post.locals.lookup other = state.locals.lookup other) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      state.clock ≤ post.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      post.clock ≤ state.clock := by
  have kept := transaction_u256_field_normal_heap_outer_frame state post tx offset arguments array index maximum input inputLength scratch frame count ceiling inputLimit
    args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove txLocal before
    outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx run
  have metadata := evaluateHOLFiniteState_metadata state
    (.seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments)
      (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v"))))
  have bounded := evaluate_transaction_u256_field_bounded state (ofString "v")
    (.op .add [.var .local (ofString "tx"),.const offset]) arguments array index maximum input inputLength scratch frame count.toNat ceiling inputLimit
    args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  rw [run] at metadata bounded
  exact ⟨kept.1,kept.2.1,kept.2.2.1,kept.2.2.2,metadata.1,metadata.2.1,bounded.1,bounded.2.1⟩

#print axioms transaction_u256_field_normal_heap_runtime_frame
end InitECandidate.Runtime
