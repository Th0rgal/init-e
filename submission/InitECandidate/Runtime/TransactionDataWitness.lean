import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionDataFieldPrefix
import InitECandidate.Runtime.TransactionDataFieldGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_decode_witness_after_data {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 200 < array.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionDataField = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index + 1 ∧ next.heap = valid.heap := by
  have retained := transaction_data_field_normal_prefix state post array count valid.index tx input inputLength scratch frame ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.txLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena arrayBelow headerBefore budget run
  obtain ⟨scratchFinal,frameFinal,heapSame⟩ := transaction_data_field_normal_globals state post array count valid.index input inputLength scratch frame ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive
    scratchBelow valid.arena budget run
  have locals := transaction_data_field_other_local state post
  have advanced := transactionDataField_increments state post valid.index valid.indexLocal run
  have metadata := evaluateHOLFiniteState_metadata state transactionDataField
  rw [run] at metadata
  have nextNat : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  refine ⟨⟨valid.index + 1,valid.heap,
    (locals _ (by decide) run).trans valid.arrayLocal,(locals _ (by decide) run).trans valid.txLocal,
    (locals _ (by decide) run).trans valid.typeLocal,advanced,?_,retained,scratchFinal,frameFinal,heapSame.trans valid.heapGlobal,
    metadata.1.trans valid.code,?_,?_,valid.heapBound,valid.heapAligned,valid.inputBeforeHeap,valid.arrayBeforeHeap⟩,rfl,rfl⟩
  · rw [nextNat]; omega
  · intro address low high
    rw [metadata.2.1]
    exact valid.arena address low high
  · intro address low high
    rw [metadata.2.1]
    exact valid.heapArena address low high

#print axioms transaction_decode_witness_after_data
end InitECandidate.Runtime
