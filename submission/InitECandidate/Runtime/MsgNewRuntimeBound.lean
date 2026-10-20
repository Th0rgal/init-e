import InitECandidate.Runtime.VmFn_msg_new_scratch
import InitECandidate.Runtime.OriginalPtSegCode
import InitECandidate.Runtime.AllocationUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Complete original heap message constructor, including allocation failure
and all actual memory-error outcomes of its fixed 176-byte zeroing call. -/
theorem msg_new_fun_bounded : FunBounded (ofString "msg_new") 41 := by
 have allocator : FunBounded (ofString "alloc") 1 := by
  refine ⟨[(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one,originalRuntimeCode_allocation_lookup,?_⟩
  intro F s code budget
  have bounded:=evaluate_source_alloc_uniform_bounded s code budget
  exact ⟨bounded.1,bounded.2.1,bounded.2.2.1⟩
 refine ⟨[],sourceFunctionBody Guest.guestFn_msg_new,.one,originalRuntimeCode_msgNew_lookup,?_⟩
 rw [sourceFunctionBody_eq_structural]
 apply ProgBounded.weaken
 · vm_bound [allocator]
 · decide
#print axioms msg_new_fun_bounded
end InitECandidate.Runtime
