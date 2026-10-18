import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionNonceFieldHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful scalar field leaves the decoder index and heap unchanged. -/
theorem transaction_decode_heap_witness_after_nonce {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 16 + 24 < array.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionNonceField = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index ∧ next.heap = valid.heap := by
  have kept := transaction_nonce_field_normal_heap_frame state post array valid.index input inputLength scratch frame count ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive
    scratchBelow valid.arena budget arrayFits arrayAbove tx valid.txLocal headerBefore run
  have locals := transaction_nonce_field_other_local state post
  have metadata := evaluateHOLFiniteState_metadata state transactionNonceField
  rw [run] at metadata
  refine ⟨⟨valid.index,valid.heap,(locals _ (by decide) (by decide) run).trans valid.arrayLocal,
    (locals _ (by decide) (by decide) run).trans valid.txLocal,(locals _ (by decide) (by decide) run).trans valid.typeLocal,
    (locals _ (by decide) (by decide) run).trans valid.indexLocal,valid.indexBound,kept.2,
    (kept.1 _).trans valid.scratchGlobal,(kept.1 _).trans valid.frameGlobal,(kept.1 _).trans valid.heapGlobal,
    metadata.1.trans valid.code,?_,?_,valid.heapBound,valid.heapAligned,valid.inputBeforeHeap,valid.arrayBeforeHeap⟩,rfl,rfl⟩
  · intro address low high
    rw [metadata.2.1]
    exact valid.arena address low high
  · intro address low high
    rw [metadata.2.1]
    exact valid.heapArena address low high

#print axioms transaction_decode_heap_witness_after_nonce
end InitECandidate.Runtime
