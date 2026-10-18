import InitECandidate.Runtime.TransactionU256Witness
import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionU256FieldHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful scalar field leaves the decoder index and heap unchanged. -/
theorem transaction_decode_heap_witness_after_u256 {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (offset maximum : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word valid.index),.val (.word maximum)])
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + offset.toNat + 24 < array.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (run : evaluateHOLFiniteState state (transactionU256Field offset arguments) = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index ∧ next.heap = valid.heap := by
  have kept := transaction_u256_field_normal_heap_frame state post tx offset arguments array valid.index maximum input inputLength scratch frame count ceiling inputLimit
    args valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena
    budget arrayFits arrayAbove valid.txLocal headerBefore run
  have metadata := evaluateHOLFiniteState_metadata state (transactionU256Field offset arguments)
  rw [run] at metadata
  refine ⟨⟨valid.index,valid.heap,(kept.2.2 _ (by decide)).trans valid.arrayLocal,
    (kept.2.2 _ (by decide)).trans valid.txLocal,(kept.2.2 _ (by decide)).trans valid.typeLocal,
    (kept.2.2 _ (by decide)).trans valid.indexLocal,valid.indexBound,kept.1,
    (kept.2.1 _).trans valid.scratchGlobal,(kept.2.1 _).trans valid.frameGlobal,(kept.2.1 _).trans valid.heapGlobal,
    metadata.1.trans valid.code,?_,?_,valid.heapBound,valid.heapAligned,valid.inputBeforeHeap,valid.arrayBeforeHeap⟩,rfl,rfl⟩
  · intro address low high
    rw [metadata.2.1]
    exact valid.arena address low high
  · intro address low high
    rw [metadata.2.1]
    exact valid.heapArena address low high

#print axioms transaction_decode_heap_witness_after_u256
end InitECandidate.Runtime
