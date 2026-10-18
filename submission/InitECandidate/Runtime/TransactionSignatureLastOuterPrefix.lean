import InitECandidate.Runtime.TransactionSignatureLastBound
import InitECandidate.Runtime.TransactionU256FieldReturnedOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_signature_last_returned_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat) (filledBound : filled < 2^64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : (index + 2#64).toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (tx outerArray outerCount outerInput outerLength : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (fits : tx.toNat + 352 + 24 < 2^64)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionSignatureLast = (some (.returned value),post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionSignatureLastArguments =
      some [.val (.word array),.val (.word (index + 2#64)),.val (.word (32 : BitVec 64))] := by
    simp [transactionSignatureLastArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have filledExact : (BitVec.ofNat 64 filled).toNat = filled := Nat.mod_eq_of_lt filledBound
  rw [source_transaction_signature_last] at run
  exact transaction_u256_field_returned_outer_prefix state post tx 352 transactionSignatureLastArguments
    array (index + 2#64) 32 input inputLength scratch frame (BitVec.ofNat 64 filled) ceiling inputLimit args
    (by simpa only [filledExact] using valid)
    (by simpa only [filledExact] using inside)
    inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
    outerArray outerCount outerInput outerLength outerValid outerBelow txLocal beforeTx fits value run

#print axioms transaction_signature_last_returned_outer_prefix
end InitECandidate.Runtime
