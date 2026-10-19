import InitECandidate.Runtime.ScratchAllocationBodyBound
import InitECandidate.Runtime.ScratchAllocationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual returned scratch allocation consumes at least its requested bytes.
The request and rounded-end checks are derived from the original execution;
no successful-space hypothesis is supplied by the caller. -/
theorem scratch_allocation_returned_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer size frame : BitVec 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (sizeLocal : s.locals.lookup (ofString "n") = some (.val (.word size)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ pointer) (code : s.code = originalRuntimeCode) (ticks : 1 ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_scratch_alloc) =
      (some (.returned value),post)) :
    value = .val (.word (scratchAllocationEnd pointer size)) ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd pointer size))) ∧
      frame.toNat ≤ (scratchAllocationEnd pointer size).toNat ∧
      (scratchAllocationEnd pointer size).toNat + size.toNat ≤ pointer.toNat ∧
      post.memory = s.memory ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code := by
  obtain ⟨result,out,bodyRun,_,_,_,_,returns⟩ := evaluate_scratch_alloc_body_bounded s pointer size frame
    scratchGlobal sizeLocal frameGlobal code ticks
  have resultEq := (Prod.mk.inj (bodyRun.symm.trans run)).1
  obtain ⟨word,request,within⟩ := returns value resultEq
  obtain ⟨actual,success,global,_,memory,installed,domain,_,endian,_⟩ :=
    evaluate_source_scratch_alloc_success s pointer size frame scratchGlobal sizeLocal frameGlobal request within
  have postEq := (Prod.mk.inj (run.symm.trans success)).2
  have requested := BitVec.le_def.mp request
  rw [BitVec.toNat_sub_of_le ordered] at requested
  have fits : size.toNat ≤ pointer.toNat := by omega
  refine ⟨word,?_,BitVec.le_def.mp within,scratchAllocationEnd_before pointer size fits,?_,?_,?_,?_⟩
  all_goals rw [postEq]
  · exact global
  · exact memory
  · exact domain
  · exact endian
  · exact installed

/-- Every successful parser-frame allocation consumes 88 bytes of the
monotonically descending scratch arena. -/
theorem scratch_parser_frame_consumes_88 {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer frame : BitVec 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (sizeLocal : s.locals.lookup (ofString "n") = some (.val (.word (88#64))))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ pointer) (code : s.code = originalRuntimeCode) (ticks : 1 ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_scratch_alloc) =
      (some (.returned value),post)) :
    ∃ next : BitVec 64, post.globals.lookup (ofString "scratch_ptr") = some (.val (.word next)) ∧
      frame.toNat ≤ next.toNat ∧ next.toNat + 88 ≤ pointer.toNat := by
  obtain ⟨_,global,lower,consumed,_⟩ := scratch_allocation_returned_progress s post pointer 88 frame value
    scratchGlobal sizeLocal frameGlobal ordered code ticks run
  exact ⟨scratchAllocationEnd pointer 88,global,lower,consumed⟩

#print axioms scratch_allocation_returned_progress
#print axioms scratch_parser_frame_consumes_88
end InitECandidate.Runtime
