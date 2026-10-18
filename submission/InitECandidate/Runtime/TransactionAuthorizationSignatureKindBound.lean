import InitECandidate.Runtime.TransactionAuthorizationSignatureBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A bound for actual authorization decoding followed by all three signature fields, including errors. -/
theorem transaction_authorization_signature_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 4#64 then 1 else 0) + 3 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 248 ≤ frame.toNat)
    (budget : transactionAuthorizationSignatureCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionAuthorizationSignature
    state.clock ≤ evaluated.2.clock + transactionAuthorizationSignatureCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := txListItemAuthorizationCost inputLength.toNat
  let tail := 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668)
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  have inside : valid.index.toNat < count.toNat := by omega
  have heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by omega
  have bounded := evaluate_transaction_authorization_branch_bounded state array valid.index input inputLength scratch frame valid.heap count.toNat ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
    valid.inputBeforeHeap heapBeforeFrame valid.heapAligned reserve firstBudget
  unfold transactionAuthorizationSignature
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state transactionAuthorizationBranch with
  | mk result middle =>
    rw [run] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some result =>
      exact ⟨by dsimp [transactionAuthorizationSignatureCost,first] at *; omega,bounded.2.1,bounded.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,_,space,futureTicks⟩ := transaction_decode_after_authorization_reserves state middle
        array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive
        scratchBelow countLimit arrayBelow (by omega) (inputLength.toNat * 16) tail (Nat.le_refl _)
        (by omega) ticks run
      have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
        rfl
      have nextFields : next.index.toNat + 3 ≤ count.toNat := by
        rw [indexEqual]
        split
        · rename_i selected
          rw [if_pos selected] at fields
          rw [addOne]; omega
        · rename_i skipped
          rw [if_neg skipped] at fields
          omega
      have remaining := transaction_signature_witness_bounded middle array count tx kind input inputLength scratch frame ceiling inputLimit
        next nextFields headerBefore arrayBelow inputBound limitBound orderedFrame framePositive scratchBelow futureTicks
      exact ⟨by dsimp [transactionAuthorizationSignatureCost,first,tail] at *; omega,
        Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_authorization_signature_bounded_by_kind
end InitECandidate.Runtime
