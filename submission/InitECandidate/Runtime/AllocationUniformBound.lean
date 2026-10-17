import InitECandidate.Runtime.AllocationFinishBound
import InitECandidate.Runtime.PanDecUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Either the original first trap check terminates, or it leaves the state
unchanged for the rounded-end declaration and final check. -/
theorem evaluate_allocationAfterPointer_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state allocationAfterPointer
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  have tail := evaluate_dec_one_uniform_bounded state (ofString "q") allocationEndExpression allocationFinish 1
    (fun word => evaluate_allocationFinish_bounded (setVarHOLFinite (ofString "q") (.val (.word word)) state) code ticks)
  obtain ⟨result,post,run,cost,remaining,noTimeout,normal,_⟩ := evaluate_conditional_trap_bounded state
    allocationRequestCheck 1 code ticks
  rw [allocationAfterPointer,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have same := normal rfl
    subst post
    exact tail
  | some stopped =>
    dsimp only
    exact ⟨cost,remaining,noTimeout,by simp⟩

/-- Complete original allocator runtime bound for arbitrary locals and
heap globals, including invalid values, overflow guards and trap rejection. -/
theorem evaluate_source_alloc_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_alloc)
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  rw [source_alloc_body]
  exact evaluate_dec_one_uniform_bounded state (ofString "p") (.var .global (ofString "heap_ptr")) allocationAfterPointer 1
    (fun word => evaluate_allocationAfterPointer_uniform_bounded (setVarHOLFinite (ofString "p") (.val (.word word)) state) code ticks)

#print axioms evaluate_allocationAfterPointer_uniform_bounded
#print axioms evaluate_source_alloc_uniform_bounded
end InitECandidate.Runtime
