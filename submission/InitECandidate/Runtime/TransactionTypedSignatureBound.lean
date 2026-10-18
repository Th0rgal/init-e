import InitECandidate.Runtime.TransactionBlobSignatureBound
import InitECandidate.Runtime.TransactionAccessReserves
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionTypedSignature : ProgHOL 64 :=
  .seq transactionAccessBranch transactionBlobSignature

theorem source_transaction_typed_signature : transactionAt 36 = transactionTypedSignature := by
  rw [transactionTypedSignature,← source_transaction_blob_signature]
  simp only [transactionAccessBranch,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def transactionTypedSignatureCost (length : Nat) : Nat :=
  txListItemAccessCost length + transactionBlobSignatureCost length

/-- The original suffix from access-list decoding through all signature fields. -/
theorem transaction_typed_signature_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 7 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionTypedSignatureCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionTypedSignature
    state.clock ≤ evaluated.2.clock + transactionTypedSignatureCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := txListItemAccessCost inputLength.toNat
  let tail := transactionBlobSignatureCost inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  have inside : valid.index.toNat < count.toNat := by omega
  have heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by omega
  have accessReserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat := by
    omega
  have bounded := evaluate_transaction_access_branch_bounded state array valid.index input inputLength scratch frame valid.heap count.toNat ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound (by omega) valid.heapArena
    valid.inputBeforeHeap heapBeforeFrame valid.heapAligned accessReserve firstBudget
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
      obtain ⟨next,indexEqual,_,space,futureTicks⟩ := transaction_decode_after_access_reserves state middle
        array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive
        scratchBelow (by omega) arrayBelow (by omega) (inputLength.toNat * 296 + 7) tail (by omega)
        (by omega) ticks run
      have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
        rfl
      have nextFields : next.index.toNat + 6 ≤ count.toNat := by
        rw [indexEqual]
        split
        · omega
        · rw [addOne]; omega
      have remaining := transaction_blob_signature_bounded middle array count tx kind input inputLength scratch frame ceiling inputLimit
        next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore (by omega) futureTicks
      exact ⟨by dsimp [transactionTypedSignatureCost,first,tail] at *; omega,
        Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_typed_signature_bounded
end InitECandidate.Runtime
