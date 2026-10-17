import InitECandidate.Runtime.ScratchAllocationRoundedFailure
import InitECandidate.Runtime.ScratchAllocationSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original scratch allocator body terminates within one source tick
for every typed request, whether allocation succeeds or either space check fails. -/
theorem evaluate_scratch_alloc_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size frame : BitVec 64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_scratch_alloc) = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → value = .val (.word (scratchAllocationEnd pointer size)) ∧
        size ≤ pointer - frame ∧ frame ≤ scratchAllocationEnd pointer size) := by
  by_cases request : size ≤ pointer - frame
  · by_cases within : frame ≤ scratchAllocationEnd pointer size
    · obtain ⟨post,run,_,clock,_⟩ := evaluate_source_scratch_alloc_success state pointer size frame
        scratchGlobal sizeLocal frameGlobal request within
      refine ⟨_,post,run,by omega,by omega,by simp,by simp,?_⟩
      intro value equal
      exact ⟨PanSemResultExact.returned.inj (Option.some.inj equal.symm),request,within⟩
    · have failed : (scratchAllocationEnd pointer size).toNat < frame.toNat := by
        have denied : ¬frame.toNat ≤ (scratchAllocationEnd pointer size).toNat := by
          intro le; exact within (BitVec.le_def.mpr le)
        omega
      obtain ⟨result,post,run,clock,noTimeout,terminal,noReturn⟩ :=
        evaluate_source_scratch_alloc_rounded_failure state pointer size frame scratchGlobal sizeLocal frameGlobal
          request failed code ticks
      exact ⟨result,post,run,by omega,by omega,noTimeout,terminal,
        by intro value equal; exact False.elim (noReturn value equal)⟩
  · have failed : (pointer - frame).toNat < size.toNat := by
      have denied : ¬size.toNat ≤ (pointer - frame).toNat := by
        intro le; exact request (BitVec.le_def.mpr le)
      omega
    obtain ⟨result,post,run,clock,noTimeout,terminal,noReturn⟩ :=
      evaluate_source_scratch_alloc_request_failure state pointer size frame scratchGlobal sizeLocal frameGlobal
        failed code ticks
    exact ⟨result,post,run,by omega,by omega,noTimeout,terminal,
      by intro value equal; exact False.elim (noReturn value equal)⟩

#print axioms evaluate_scratch_alloc_body_bounded
end InitECandidate.Runtime
