import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionSignatureFirstHeapBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A concrete decoder witness and three remaining fields supply the signature suffix premises. -/
theorem transaction_signature_witness_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 3 ≤ count.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (budget : 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionSignatureFirst
    state.clock ≤ evaluated.2.clock + 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have addTwo : (valid.index + 2).toNat = valid.index.toNat + 2 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 2 < 2^64; omega)]
    rfl
  exact evaluate_transaction_signature_first_heap_bounded state array count valid.index tx input inputLength scratch frame ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices (by change (valid.index + 2).toNat < count.toNat; rw [addTwo]; omega) (by change (valid.index + 1).toNat < count.toNat; rw [addOne]; omega) (by omega)
    valid.txLocal (by omega) arrayFits arrayAbove inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive
    scratchBelow valid.arena budget

#print axioms transaction_signature_witness_heap_bounded
end InitECandidate.Runtime
