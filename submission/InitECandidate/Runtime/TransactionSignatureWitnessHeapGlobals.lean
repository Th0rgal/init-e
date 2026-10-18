import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionSignatureFirstHeapGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A concrete decoder witness and three remaining fields supply the signature suffix premises. -/
theorem transaction_signature_witness_returned_heap_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 3 ≤ count.toNat)
    (headerBefore : tx.toNat + 376 < array.toNat)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (budget : 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64) (watchedAbove : ceiling ≤ watchedArray.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (headerFits : tx.toNat + 376 < 2^64)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionSignatureFirst = (some (.returned value),post)) :
    (∀ watched, post.globals.lookup watched = state.globals.lookup watched) := by
  have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have addTwo : (valid.index + 2).toNat = valid.index.toNat + 2 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 2 < 2^64; omega)]
    rfl
  exact transaction_signature_first_returned_heap_globals state post array count valid.index tx input inputLength scratch frame ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices (by change (valid.index + 2).toNat < count.toNat; rw [addTwo]; omega) (by change (valid.index + 1).toNat < count.toNat; rw [addOne]; omega) (by omega)
    valid.txLocal (by omega) arrayFits arrayAbove inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive
    scratchBelow valid.arena budget
    watchedArray watchedCount watchedInput watchedLength watchedValid watchedFits watchedAbove beforeTx headerFits value run

#print axioms transaction_signature_witness_returned_heap_globals
end InitECandidate.Runtime
