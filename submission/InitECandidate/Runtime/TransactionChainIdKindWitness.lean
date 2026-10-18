import InitECandidate.Runtime.TransactionChainIdWitness
import InitECandidate.Runtime.TransactionChainIdKindIndex
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_decode_witness_after_chain_id_by_kind {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : 0 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 8 < array.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionChainIdBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = (if kind = 0#64 then valid.index else 1) ∧ next.heap = valid.heap := by
  obtain ⟨next,_,heapEqual⟩ := transaction_decode_witness_after_chain_id state post array count tx kind input inputLength scratch frame ceiling inputLimit
    valid inside inputBound limitBound orderedFrame framePositive scratchBelow arrayBelow headerBefore budget run
  have binding := transaction_chain_id_index_by_kind state post valid.index kind valid.indexLocal valid.typeLocal run
  have equal : next.index = (if kind = 0#64 then valid.index else 1) :=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.indexLocal.symm.trans binding)))
  exact ⟨next,equal,heapEqual⟩

#print axioms transaction_decode_witness_after_chain_id_by_kind
end InitECandidate.Runtime
