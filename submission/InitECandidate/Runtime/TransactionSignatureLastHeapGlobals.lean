import InitECandidate.Runtime.TransactionSignatureLastHeapBound
import InitECandidate.Runtime.TransactionU256FieldReturnedHeapGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_signature_last_returned_heap_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (arrayFits : array.toNat + filled * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (before : tx.toNat + 352 + 24 < array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionSignatureLast = (some (.returned value),post)) :
    (∀ watched, post.globals.lookup watched = state.globals.lookup watched) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionSignatureLastArguments =
      some [.val (.word array),.val (.word (index + 2#64)),.val (.word (32 : BitVec 64))] := by
    simp [transactionSignatureLastArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have filledExact : (BitVec.ofNat 64 filled).toNat = filled := Nat.mod_eq_of_lt filledBound
  rw [source_transaction_signature_last] at run
  exact transaction_u256_field_returned_heap_globals state post tx 352 transactionSignatureLastArguments
    array (index + 2#64) 32 input inputLength scratch frame (BitVec.ofNat 64 filled) ceiling inputLimit args
    (by simpa only [filledExact] using valid)
    (by simpa only [filledExact] using inside)
    inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
    (by simpa only [filledExact] using arrayFits) arrayAbove txLocal before value run

#print axioms transaction_signature_last_returned_heap_globals
end InitECandidate.Runtime
