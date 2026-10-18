import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionChainIdHeapFrame
import InitECandidate.Runtime.TransactionChainIdIndex
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Chain-ID decoding retains the heap and advances the index by at most one. -/
theorem transaction_decode_heap_witness_after_chain_id {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : 0 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 8 < array.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionChainIdBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index.toNat ≤ valid.index.toNat + 1 ∧ next.heap = valid.heap := by
  have kept := transaction_chain_id_normal_heap_frame state post array input inputLength scratch frame count ceiling inputLimit
    valid.arrayLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive
    scratchBelow valid.arena budget arrayFits arrayAbove tx valid.txLocal headerBefore run
  have locals := transaction_chain_id_other_local state post
  have metadata := evaluateHOLFiniteState_metadata state transactionChainIdBranch
  rw [run] at metadata
  obtain ⟨index,binding,indexBound,upper⟩ : ∃ index : BitVec 64,
      post.locals.lookup (ofString "k") = some (.val (.word index)) ∧
      index.toNat ≤ count.toNat ∧ index.toNat ≤ valid.index.toNat + 1 := by
    rcases transaction_chain_id_index state post valid.index valid.indexLocal run with unchanged | initialized
    · exact ⟨valid.index,unchanged,valid.indexBound,by omega⟩
    · exact ⟨1,initialized,by change 1 ≤ count.toNat; omega,by change 1 ≤ valid.index.toNat + 1; omega⟩
  refine ⟨⟨index,valid.heap,(locals _ (by decide) (by decide) run).trans valid.arrayLocal,
    (locals _ (by decide) (by decide) run).trans valid.txLocal,(locals _ (by decide) (by decide) run).trans valid.typeLocal,
    binding,indexBound,kept.2,
    (kept.1 _).trans valid.scratchGlobal,(kept.1 _).trans valid.frameGlobal,(kept.1 _).trans valid.heapGlobal,
    metadata.1.trans valid.code,?_,?_,valid.heapBound,valid.heapAligned,valid.inputBeforeHeap,valid.arrayBeforeHeap⟩,upper,rfl⟩
  · intro address low high
    rw [metadata.2.1]
    exact valid.arena address low high
  · intro address low high
    rw [metadata.2.1]
    exact valid.heapArena address low high

#print axioms transaction_decode_heap_witness_after_chain_id
end InitECandidate.Runtime
