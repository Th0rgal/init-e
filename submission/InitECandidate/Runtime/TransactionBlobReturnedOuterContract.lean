import InitECandidate.Runtime.TransactionBlobReserves
import InitECandidate.Runtime.TransactionBlobBranchOuterPrefix
import InitECandidate.Runtime.TransactionBlobSignatureBound
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_blob_returned_outer_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 2 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 264 < array.toNat)
    (futureSpace futureTicks : Nat)
    (space : valid.heap.toNat + inputLength.toNat * 48 + futureSpace ≤ frame.toNat)
    (ticks : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat + futureTicks ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionBlobSignature = (some (.returned value),final)) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState post transactionAuthorizationSignature = (some (.returned value),final) ∧
      RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat ∧
      ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
        next.index = (if kind = 3#64 then valid.index + 2 else valid.index) ∧
        valid.heap.toNat ≤ next.heap.toNat ∧ next.heap.toNat + futureSpace ≤ frame.toNat ∧ futureTicks ≤ post.clock := by
  have noReturn := evaluate_noDirectReturn transactionBlobBranch (by rw [source_transaction_blob_branch,source_transaction_blob_body,source_transaction_blob_extraction,source_transaction_blob_decode]; rfl) state value
  unfold transactionBlobSignature at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state transactionBlobBranch with
  | mk result post =>
    rw [branchRun] at run noReturn
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      obtain ⟨next,indexEqual,lower,nextSpace,nextTicks⟩ := transaction_decode_after_blob_reserves state post
        array count tx kind input inputLength scratch frame ceiling inputLimit valid fields inputBound limitBound orderedFrame framePositive scratchBelow
        countLimit arrayBeforeFrame headerBefore futureSpace futureTicks space ticks branchRun
      have heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by omega
      have shifted : (valid.index + 1).toNat = valid.index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
        rfl
      have inside : (valid.index + 1).toNat < count.toNat := by rw [shifted]; omega
      have retained := transaction_blob_branch_normal_outer_prefix state post array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit
        valid.arrayLocal valid.indexLocal valid.slices inside (by omega) valid.txLocal (by change tx.toNat + 224 + 24 < array.toNat; omega)
        arrayBeforeFrame inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena
        valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame
        ((Nat.le_add_right _ futureTicks).trans ticks) valid.arrayBeforeHeap headerBefore
        watchedArray watchedCount watchedInput watchedLength watchedValid watchedBeforeFrame
        (by
          have txBeforeArray : tx.toNat ≤ array.toNat := by omega
          exact beforeTx.trans (txBeforeArray.trans ((Nat.le_add_right _ _).trans valid.arrayBeforeHeap))) beforeTx valid.heapAligned branchRun
      exact ⟨post,run,retained,next,indexEqual,lower,nextSpace,nextTicks⟩


#print axioms transaction_blob_returned_outer_contract
end InitECandidate.Runtime
