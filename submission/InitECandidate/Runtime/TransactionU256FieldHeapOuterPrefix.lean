import InitECandidate.Runtime.TxScalarU256LocalCallHeapOuterPrefix
import InitECandidate.Runtime.TxScalarU256LocalCallValue
import InitECandidate.Runtime.TransactionU256HeaderOuterPrefix
import InitECandidate.Runtime.LocalCallSuccessOtherLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful scalar assignment and header storage retain slices for the next field. -/
theorem transaction_u256_field_normal_heap_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (fits : tx.toNat + offset.toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments)
        (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v")))) = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") arguments) with
  | mk result middle =>
    rw [callRun] at run
    cases result with
    | some result => cases run
    | none =>
      have retained := txScalarU256_local_call_heap_outer_prefix state middle (ofString "v") arguments array index maximum input inputLength scratch frame count ceiling inputLimit
        args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget outerArray outerCount outerInput outerLength outerValid outerFits outerAbove callRun
      obtain ⟨first,second,third,fourth,valueLocal⟩ := txScalarU256_local_call_value state middle (ofString "v") arguments array index maximum args code callRun
      have other := evaluate_local_call_success_other_locals state (ofString "tx_scalar_u256") (ofString "v") arguments (by rw [callRun])
      have atTx : middle.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
        have kept := other (ofString "tx") (by decide)
        rw [callRun] at kept
        exact kept.trans txLocal
      have kept := transaction_u256_header_outer_prefix middle tx offset outerArray outerCount outerInput outerLength
        (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) atTx valueLocal
        (by simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]) retained before fits
      dsimp only at run
      rw [run] at kept
      exact kept

#print axioms transaction_u256_field_normal_heap_outer_prefix
end InitECandidate.Runtime
