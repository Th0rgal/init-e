import InitECandidate.Runtime.AllocationSuccess
import InitECandidate.Runtime.AllocationFailureNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The heap limit is eight-byte aligned. A request passing the first guard
cannot fail the rounded-end guard when the initial pointer is in bounds. -/
theorem allocationEnd_within_heap (pointer size : BitVec 64)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer) :
    (allocationEnd pointer size).toNat ≤ 33806089496 := by
  have sum := allocationGuard_sum_bound pointer size pointerBound request
  have cover := allocationEnd_covers pointer size sum
  omega

/-- Complete original allocator body for every 64-bit request, either returning
an allocated pointer or terminating through the actual trap path. -/
theorem evaluate_source_alloc_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (pointerBound : pointer.toNat ≤ 33806089496) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_alloc) = (result,post) ∧
      result ≠ none ∧ state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock := by
  by_cases request : size ≤ (33806089496 : BitVec 64) - pointer
  · obtain ⟨post,run,_,clock,_⟩ := evaluate_source_alloc_success state pointer size heap sizeLocal request
      (allocationEnd_within_heap pointer size pointerBound request)
    exact ⟨_,post,run,by simp,by omega,by omega⟩
  · have rejected : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat := by
      have notLe : ¬size.toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat := fun le => request (BitVec.le_def.mpr le)
      omega
    obtain ⟨result,post,run,terminal,_,clock⟩ := evaluate_source_alloc_request_failure_no_return state pointer size code heap sizeLocal rejected
    exact ⟨result,post,run,terminal,by omega,by omega⟩

#print axioms allocationEnd_within_heap
#print axioms evaluate_source_alloc_bounded
end InitECandidate.Runtime
