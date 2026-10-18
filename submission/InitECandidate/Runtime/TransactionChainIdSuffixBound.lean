import InitECandidate.Runtime.TransactionChainIdWitness
import InitECandidate.Runtime.TransactionChainIdBound
import InitECandidate.Runtime.TransactionNonceScopeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionChainIdSuffixCost (length : Nat) : Nat :=
  (length * ((2 * length + 1) * 15 + 19) + 92643) + transactionNonceSuffixCost length

/-- Chain-ID decoding and the original scoped nonce suffix have a combined source-clock bound. -/
theorem transaction_chain_id_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 15 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionChainIdSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 17)
    state.clock ≤ evaluated.2.clock + transactionChainIdSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643
  let tail := transactionNonceSuffixCost inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  have inside : 0 < count.toNat := by omega
  have bounded := evaluate_transaction_chain_id_bounded state array input inputLength scratch frame count.toNat ceiling inputLimit
    valid.arrayLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena firstBudget
  rw [source_transaction_chain_id]
  change state.clock ≤ (evaluateHOLFiniteState state (.seq transactionChainIdBranch (transactionAt 18))).2.clock + transactionChainIdSuffixCost inputLength.toNat ∧
    (evaluateHOLFiniteState state (.seq transactionChainIdBranch (transactionAt 18))).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (.seq transactionChainIdBranch (transactionAt 18))).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state transactionChainIdBranch with
  | mk result middle =>
    rw [run] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some result =>
      exact ⟨by dsimp [transactionChainIdSuffixCost,first] at *; omega,bounded.2.1,bounded.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,heapEqual⟩ := transaction_decode_witness_after_chain_id state middle array count tx kind input inputLength scratch frame ceiling inputLimit
        valid inside inputBound limitBound orderedFrame framePositive scratchBelow arrayBelow (by omega) firstBudget run
      have nextFields : next.index.toNat + 14 ≤ count.toNat := by omega
      have futureTicks : tail ≤ middle.clock := by have spent := bounded.1; omega
      have remaining := transaction_nonce_scope_bounded middle array count tx kind input inputLength scratch frame ceiling inputLimit
        next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore (by rw [heapEqual]; exact reserve) futureTicks
      exact ⟨by dsimp [transactionChainIdSuffixCost,first,tail] at *; omega,
        Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_chain_id_suffix_bounded
end InitECandidate.Runtime
