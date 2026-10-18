import InitECandidate.Runtime.TransactionAccessHeapClockReserve
import InitECandidate.Runtime.TransactionAccessBranchHeapBound
import InitECandidate.Runtime.TransactionTypedSignatureBound
import InitECandidate.Runtime.TransactionBlobSignatureHeapKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original suffix from access-list decoding through all signature fields. -/
theorem transaction_typed_signature_heap_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 3 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (budget : transactionTypedSignatureCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionTypedSignature
    state.clock ≤ evaluated.2.clock + transactionTypedSignatureCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := txListItemAccessCost inputLength.toNat
  let tail := transactionBlobSignatureCost inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  have inside : valid.index.toNat < count.toNat := by omega
  have bounded := evaluate_transaction_access_branch_heap_bounded state array valid.index input inputLength scratch frame valid.heap count.toNat ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound (by omega) valid.heapArena
    valid.inputBeforeHeap inputBeforeFrame (by have h := valid.arrayBeforeHeap; omega) valid.heapAligned firstBudget
  unfold transactionTypedSignature
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state transactionAccessBranch with
  | mk result middle =>
    rw [run] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some result =>
      exact ⟨by dsimp [transactionTypedSignatureCost,first] at *; omega,bounded.2.1,bounded.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,_,futureTicks⟩ := transaction_decode_after_access_heap_clock_reserve state middle
        array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive
        scratchBelow (by omega) arrayAbove inputBeforeFrame (by omega) tail ticks run
      have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
        rfl
      have nextFields : next.index.toNat + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 3 ≤ count.toNat := by
        rw [indexEqual]
        split
        · rename_i skipped
          rw [if_pos skipped] at fields
          omega
        · rename_i selected
          rw [if_neg selected] at fields
          rw [addOne]; omega
      have remaining := transaction_blob_signature_heap_bounded_by_kind middle array count tx kind input inputLength scratch frame ceiling inputLimit
        next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore futureTicks
      exact ⟨by dsimp [transactionTypedSignatureCost,first,tail] at *; omega,
        Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_typed_signature_heap_bounded_by_kind
end InitECandidate.Runtime
