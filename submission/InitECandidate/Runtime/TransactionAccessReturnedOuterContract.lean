import InitECandidate.Runtime.TransactionAccessReserves
import InitECandidate.Runtime.TransactionAccessBranchOuterPrefix
import InitECandidate.Runtime.TransactionTypedSignatureBound
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_access_returned_outer_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 216 < array.toNat)
    (futureSpace futureTicks : Nat)
    (futureWorkspace : inputLength.toNat * 32 + 7 ≤ futureSpace)
    (space : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + futureSpace ≤ frame.toNat)
    (ticks : txListItemAccessCost inputLength.toNat + futureTicks ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionTypedSignature = (some (.returned value),final)) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState post transactionBlobSignature = (some (.returned value),final) ∧
      RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat ∧
      ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
        next.index = (if kind = 0#64 then valid.index else valid.index + 1) ∧
        valid.heap.toNat ≤ next.heap.toNat ∧ next.heap.toNat + futureSpace ≤ frame.toNat ∧ futureTicks ≤ post.clock := by
  have noReturn := evaluate_noDirectReturn transactionAccessBranch (by rw [source_transaction_access_branch,source_transaction_access_extraction,source_transaction_access_decode]; rfl) state value
  unfold transactionTypedSignature at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state transactionAccessBranch with
  | mk result post =>
    rw [branchRun] at run noReturn
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      obtain ⟨next,indexEqual,lower,nextSpace,nextTicks⟩ := transaction_decode_after_access_reserves state post
        array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive scratchBelow
        countLimit arrayBeforeFrame headerBefore futureSpace futureTicks futureWorkspace space ticks branchRun
      have heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by omega
      have reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat := by omega
      have retained := transaction_access_branch_normal_outer_prefix state post array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit
        valid.arrayLocal valid.indexLocal valid.txLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
        orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame
        arrayBeforeFrame valid.arrayBeforeHeap watchedArray watchedCount watchedInput watchedLength watchedValid watchedBeforeFrame
        (by
          have txBeforeArray : tx.toNat ≤ array.toNat := by omega
          exact beforeTx.trans (txBeforeArray.trans ((Nat.le_add_right _ _).trans valid.arrayBeforeHeap))) beforeTx (Nat.lt_trans headerBefore array.isLt)
        valid.heapAligned reserve ((Nat.le_add_right _ futureTicks).trans ticks) branchRun
      exact ⟨post,run,retained,next,indexEqual,lower,nextSpace,nextTicks⟩

#print axioms transaction_access_returned_outer_contract
end InitECandidate.Runtime
