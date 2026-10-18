import InitECandidate.Runtime.TransactionAuthorizationHeapClock
import InitECandidate.Runtime.TransactionAuthorizationBranchHeapOuterPrefix
import InitECandidate.Runtime.TransactionAuthorizationSignatureBound
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned authorization-then-signature stage passed through a normal actual
authorization branch: the signature suffix state keeps the watched slice array,
the reconstructed transaction witness, heap growth and remaining clock, all in
the actual layout without frame reserves. -/
theorem transaction_authorization_returned_guarded_heap_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (headerBefore : tx.toNat + 280 < array.toNat)
    (futureTicks : Nat)
    (ticks : txListItemAuthorizationCost inputLength.toNat + futureTicks ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionAuthorizationSignature = (some (.returned value),final)) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState post transactionSignatureFirst = (some (.returned value),final) ∧
      RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat ∧
      ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
        next.index = (if kind = 4#64 then valid.index + 1 else valid.index) ∧
        valid.heap.toNat ≤ next.heap.toNat ∧ futureTicks ≤ post.clock ∧
        next.heap.toNat ≤ valid.heap.toNat + inputLength.toNat * 232 := by
  have noReturn := evaluate_noDirectReturn transactionAuthorizationBranch (by rw [source_transaction_authorization_branch,source_transaction_authorization_extraction,source_transaction_authorization_decode]; rfl) state value
  unfold transactionAuthorizationSignature at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state transactionAuthorizationBranch with
  | mk result post =>
    rw [branchRun] at run noReturn
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      obtain ⟨next,indexEqual,lower,upper,nextTicks⟩ := transaction_decode_after_authorization_heap_clock state post
        array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive scratchBelow
        countLimit arrayAbove headerBefore inputBeforeFrame futureTicks ticks branchRun
      have heapAbove : ceiling ≤ valid.heap.toNat := by have h := valid.arrayBeforeHeap; omega
      have arrayFits : array.toNat + count.toNat * 16 ≤ 2^64 := by
        have h := valid.arrayBeforeHeap; have b := valid.heapBound; omega
      have txBeforeArray : tx.toNat ≤ array.toNat := by omega
      have watchedBeforeHeap : watchedArray.toNat + watchedCount.toNat * 16 ≤ valid.heap.toNat :=
        beforeTx.trans (txBeforeArray.trans ((Nat.le_add_right _ _).trans valid.arrayBeforeHeap))
      have watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64 := by
        have b := valid.heapBound; omega
      have retained := transaction_authorization_branch_normal_heap_outer_prefix state post array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit
        valid.arrayLocal valid.indexLocal valid.txLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
        orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap inputBeforeFrame heapAbove
        arrayFits arrayAbove valid.arrayBeforeHeap headerBefore watchedArray watchedCount watchedInput watchedLength watchedValid watchedFits watchedAbove
        watchedBeforeHeap beforeTx valid.heapAligned ((Nat.le_add_right _ futureTicks).trans ticks) branchRun
      exact ⟨post,run,retained,next,indexEqual,lower,nextTicks,upper⟩

#print axioms transaction_authorization_returned_guarded_heap_contract
end InitECandidate.Runtime
