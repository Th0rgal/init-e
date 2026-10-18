import InitECandidate.Runtime.TransactionAuthorizationReturnedOuterContract
import InitECandidate.Runtime.TransactionSignatureWitnessOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_authorization_signature_returned_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 4 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 248 ≤ frame.toNat)
    (budget : transactionAuthorizationSignatureCost inputLength.toNat ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBelow : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (headerFits : tx.toNat + 376 < 2^64)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionAuthorizationSignature = (some (.returned value),final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  let tail := 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668)
  obtain ⟨post,tailRun,retained,next,indexEqual,_,_,nextTicks⟩ := transaction_authorization_returned_outer_contract state final
    array count tx kind input inputLength scratch frame ceiling inputLimit valid (by omega) inputBound limitBound
    orderedFrame framePositive scratchBelow countLimit arrayBelow (by omega) (inputLength.toNat * 16) tail
    (Nat.le_refl _) (by omega) budget watchedArray watchedCount watchedInput watchedLength watchedValid watchedBelow beforeTx value run
  have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have nextFields : next.index.toNat + 3 ≤ count.toNat := by
    rw [indexEqual]
    split
    · rw [addOne]; omega
    · omega
  exact transaction_signature_witness_returned_outer_prefix post final array count tx kind input inputLength scratch frame ceiling inputLimit
    next nextFields headerBefore arrayBelow inputBound limitBound orderedFrame framePositive scratchBelow nextTicks
    watchedArray watchedCount watchedInput watchedLength retained watchedBelow beforeTx headerFits value tailRun

#print axioms transaction_authorization_signature_returned_outer_prefix
end InitECandidate.Runtime
