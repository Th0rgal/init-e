import InitECandidate.Runtime.InputBlobAllocationBound
import InitECandidate.Runtime.InputBlobGuardBound
import InitECandidate.Runtime.SharedLoadControlFrame
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def inputBlobBodyCost : Nat := 16777217

theorem evaluate_inputBlob_guard_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length heapPointer : BitVec 64)
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : inputBlobBodyCost ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (inputBlobAt 2)
    state.clock ≤ evaluated.2.clock + inputBlobBodyCost ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases large : 134217712 < length.toNat
  · obtain ⟨result,run,_,spent,kept,safe⟩ := inputBlob_oversized_rejected state length atLength code large
      (by unfold inputBlobBodyCost at budget; omega)
    refine ⟨by unfold inputBlobBodyCost; omega,kept,?_⟩
    intro timedOut
    exact safe (by unfold inputBlobBodyCost at budget; omega) (Option.some.inj (run.symm.trans timedOut))
  · have small : length.toNat ≤ 134217712 := by omega
    have limit : inputBlobCopyBound length + 2 ≤ inputBlobBodyCost := by
      unfold inputBlobCopyBound inputBlobBodyCost
      omega
    rw [source_inputBlob_stages.2.2.1,evaluateHOLFiniteState_seq_line780,inputBlob_guard_accepts state length atLength small]
    dsimp only
    have bound := evaluate_inputBlob_allocation_copy_bounded state length heapPointer atLength heap heapBound code small (by omega)
    exact ⟨by have spent := bound.1; omega,bound.2⟩

theorem evaluate_inputBlob_load_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heapPointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : inputBlobBodyCost ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (inputBlobAt 1)
    state.clock ≤ evaluated.2.clock + inputBlobBodyCost ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have loaded := evaluate_shared_load_control_frame state .opW (ofString "len") (.const 1073741832)
  change (evaluateHOLFiniteState state inputBlobLengthLoad).2.clock = state.clock ∧
    ((evaluateHOLFiniteState state inputBlobLengthLoad).1 = none ∨
      (evaluateHOLFiniteState state inputBlobLengthLoad).1 = some .error ∨
      ∃ event, (evaluateHOLFiniteState state inputBlobLengthLoad).1 = some (.finalFfi event)) ∧
    (evaluateHOLFiniteState state inputBlobLengthLoad).2.globals = state.globals ∧
    (evaluateHOLFiniteState state inputBlobLengthLoad).2.memory = state.memory ∧
    (evaluateHOLFiniteState state inputBlobLengthLoad).2.memaddrs = state.memaddrs ∧
    ((evaluateHOLFiniteState state inputBlobLengthLoad).1 = none → ∃ word : BitVec 64,
      (evaluateHOLFiniteState state inputBlobLengthLoad).2.locals.lookup (ofString "len") = some (.val (.word word)) ∧
      ∀ key, key ≠ ofString "len" →
        (evaluateHOLFiniteState state inputBlobLengthLoad).2.locals.lookup key = state.locals.lookup key) at loaded
  have metadata := evaluateHOLFiniteState_metadata state inputBlobLengthLoad
  rw [source_inputBlob_stages.2.1,evaluateHOLFiniteState_seq_line780]
  cases loadRun : evaluateHOLFiniteState state inputBlobLengthLoad with
  | mk result next =>
    rw [loadRun] at loaded metadata
    dsimp only at loaded metadata ⊢
    obtain ⟨clock,control,globals,_,_,normal⟩ := loaded
    rcases control with rfl | rfl | ⟨event,rfl⟩
    · obtain ⟨length,atLength,_⟩ := normal rfl
      have bound := evaluate_inputBlob_guard_suffix_bounded next length heapPointer atLength
        (by rw [globals]; exact heap) heapBound (metadata.1.trans code) (by rw [clock]; exact budget)
      dsimp only
      exact ⟨by have spent := bound.1; omega,by have kept := bound.2.1; omega,bound.2.2⟩
    · dsimp only
      exact ⟨by omega,by omega,by simp⟩
    · dsimp only
      exact ⟨by omega,by omega,by simp⟩

/-- The complete original input reader has a uniform finite bound for every
64-bit declared length, including oversized rejection before allocation,
heap exhaustion, failed accesses and early host termination. -/
theorem evaluate_inputBlob_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heapPointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : inputBlobBodyCost ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_input_blob)
    state.clock ≤ evaluated.2.clock + inputBlobBodyCost ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  change state.clock ≤ (evaluateHOLFiniteState state (inputBlobAt 0)).2.clock + inputBlobBodyCost ∧
    (evaluateHOLFiniteState state (inputBlobAt 0)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (inputBlobAt 0)).1 ≠ some .timeOut
  rw [source_inputBlob_stages.1]
  apply evaluate_dec_word_post state (ofString "len") (.const 0) _ (0 : BitVec 64) inputBlobBodyCost
    (fun r _ => r ≠ some .timeOut) (fun _ _ _ h => h) (by simp [evalHOLExact])
  exact evaluate_inputBlob_load_suffix_bounded (setVarHOLFinite (ofString "len") (.val (.word (0 : BitVec 64))) state)
    heapPointer heap heapBound code budget

#print axioms evaluate_inputBlob_guard_suffix_bounded
#print axioms evaluate_inputBlob_load_suffix_bounded
#print axioms evaluate_inputBlob_body_bounded
end InitECandidate.Runtime
