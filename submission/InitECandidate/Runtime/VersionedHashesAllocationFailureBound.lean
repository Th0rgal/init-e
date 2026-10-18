import InitECandidate.Runtime.TransactionWrapperDeclCallAllocationFailureBound
import InitECandidate.Runtime.VersionedHashesSourceStepBound
import InitECandidate.Runtime.LoadOneWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual transaction argument loads either fail or produce exactly two words. -/
theorem transaction_slice_arguments_word_result {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arrayName indexName : MlS) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (transactionSliceArguments arrayName indexName) = none ∨
    ∃ pointer length : BitVec 64, evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) (transactionSliceArguments arrayName indexName) =
      some [.val (.word pointer),.val (.word length)] := by
  let first : ExpHOL 64 := .op .add [.var .local arrayName,.panop .mul [.var .local indexName,.const 16#64]]
  let second : ExpHOL 64 := .op .add [.var .local arrayName,.panop .mul [.var .local indexName,.const 16#64],.const 8#64]
  cases loadFirst : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one first) with
  | none =>
    dsimp only [first] at loadFirst
    exact Or.inl (by simp [transactionSliceArguments,evalListHOLFinite,evalListHOLExact,loadFirst])
  | some value =>
    dsimp only [first] at loadFirst
    obtain ⟨pointer,rfl⟩ := eval_load_one_word state first value loadFirst
    cases loadSecond : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one second) with
    | none =>
      dsimp only [second] at loadSecond
      exact Or.inl (by simp [transactionSliceArguments,evalListHOLFinite,evalListHOLExact,loadFirst,loadSecond])
    | some value =>
      dsimp only [second] at loadSecond
      obtain ⟨length,rfl⟩ := eval_load_one_word state second value loadSecond
      exact Or.inr ⟨pointer,length,by simp [transactionSliceArguments,evalListHOLFinite,evalListHOLExact,loadFirst,loadSecond]⟩

/-- Exhausted heap bounds the actual source step without any readable-slice,
input-span, scratch-arena, or successful-allocation reserve assumptions. -/
theorem evaluate_versioned_hashes_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 4 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state versionedHashesStep
    state.clock ≤ evaluated.2.clock + 4 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rcases transaction_slice_arguments_word_result state (ofString "txs") (ofString "i") with missing | ⟨pointer,length,args⟩
  · rw [evaluate_versioned_hashes_source_step_missing_arguments state missing]
    dsimp only
    exact ⟨by omega,Nat.le_refl _,by simp⟩
  · rw [source_versioned_hashes_step]
    exact evaluate_transaction_wrapper_decl_call_allocation_failure_bounded state (ofString "tx") .one
      (transactionSliceArguments (ofString "txs") (ofString "i")) _ pointer length heap args code heapGlobal request budget

#print axioms transaction_slice_arguments_word_result
#print axioms evaluate_versioned_hashes_allocation_failure_bounded
end InitECandidate.Runtime
