import InitECandidate.Runtime.TransactionAuthorizationReserves
import InitECandidate.Runtime.TransactionAuthorizationBranchOuterPrefix
import InitECandidate.Runtime.TransactionAuthorizationSignatureBound
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_authorization_returned_heap_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 280 < array.toNat)
    (futureSpace futureTicks : Nat)
    (futureWorkspace : inputLength.toNat * 16 ≤ futureSpace)
    (space : valid.heap.toNat + inputLength.toNat * 232 + futureSpace ≤ frame.toNat)
    (ticks : txListItemAuthorizationCost inputLength.toNat + futureTicks ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionAuthorizationSignature = (some (.returned value),final)) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState post transactionSignatureFirst = (some (.returned value),final) ∧
      RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat ∧
      ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
        next.index = (if kind = 4#64 then valid.index + 1 else valid.index) ∧
        valid.heap.toNat ≤ next.heap.toNat ∧ next.heap.toNat + futureSpace ≤ frame.toNat ∧ futureTicks ≤ post.clock ∧ next.heap.toNat ≤ valid.heap.toNat + inputLength.toNat * 232 := by
  have noReturn := evaluate_noDirectReturn transactionAuthorizationBranch (by rw [source_transaction_authorization_branch,source_transaction_authorization_extraction,source_transaction_authorization_decode]; rfl) state value
  unfold transactionAuthorizationSignature at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state transactionAuthorizationBranch with
  | mk result post =>
    rw [branchRun] at run noReturn
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      obtain ⟨next,indexEqual,lower,nextSpace,nextTicks⟩ := transaction_decode_after_authorization_reserves state post
        array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive scratchBelow
        countLimit arrayBeforeFrame headerBefore futureSpace futureTicks futureWorkspace space ticks branchRun
      have heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by omega
      have reserve : valid.heap.toNat + inputLength.toNat * 248 ≤ frame.toNat := by omega
      have retained := transaction_authorization_branch_normal_outer_prefix state post array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit
        valid.arrayLocal valid.indexLocal valid.txLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
        orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame
        arrayBeforeFrame valid.arrayBeforeHeap headerBefore watchedArray watchedCount watchedInput watchedLength watchedValid watchedBeforeFrame
        (by
          have txBeforeArray : tx.toNat ≤ array.toNat := by omega
          exact beforeTx.trans (txBeforeArray.trans ((Nat.le_add_right _ _).trans valid.arrayBeforeHeap)))
        beforeTx valid.heapAligned reserve ((Nat.le_add_right _ futureTicks).trans ticks) branchRun
      obtain ⟨nextHeap,binding,_,upper,_,_,_,_⟩ := transaction_authorization_branch_normal_heap_growth state post
        array count valid.index input inputLength scratch frame valid.heap ceiling inputLimit valid.arrayLocal valid.indexLocal valid.slices
        inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena
        valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame valid.heapAligned reserve
        ((Nat.le_add_right _ futureTicks).trans ticks) branchRun
      have same : next.heap = nextHeap :=
        HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.heapGlobal.symm.trans binding)))
      exact ⟨post,run,retained,next,indexEqual,lower,nextSpace,nextTicks,by rw [same]; exact upper⟩



#print axioms transaction_authorization_returned_heap_contract
end InitECandidate.Runtime
