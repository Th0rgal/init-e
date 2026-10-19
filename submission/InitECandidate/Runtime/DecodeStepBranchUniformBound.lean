import InitECandidate.Runtime.DecodeStepBranchUniformProgress
import InitECandidate.Runtime.ScratchAllocationDecCallBound
import InitECandidate.Runtime.DecodeStepArityDispatch
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- All outcomes of the actual heap-constructor plus scratch-record branch are
bounded. Both allocators' rejection paths and inaccessible stores are covered. -/
theorem runBounded_decode_step_branch_construction {F : Type} (s : PanSemStateFiniteExact 64 F)
    (scratch frame : BitVec 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (budget : 43 ≤ s.clock) :
    RunBounded s decodeStepBranchConstruction 43 := by
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 64))
  have lookup := pan_no_args_lookup s.code.lookup (ofString "node_new_branch")
    (sourceFunctionBody Guest.guestFn_node_new_branch)
    (by rw [code]; exact originalRuntimeCode_nodeNewBranch_lookup)
  have bounded := runBounded_node_new_branch_body entry code (by change 40 ≤ s.clock - 1; omega)
  have reached : Reaches s decodeStepBranchConstruction
      (fun next => next.code = originalRuntimeCode ∧
        next.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        next.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
      41 decodeStepBranchRecord := by
    rw [source_decode_step_branch_construction]
    apply bounded_decCall_reaches s (ofString "br") (ofString "node_new_branch") .one .one _ _ _ _
      HolFiniteMapExact.empty 40 _ rfl lookup (by omega) bounded
    intro value post run shapes
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_node_new_branch)
    have scratchKept := node_new_branch_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeConstructorWorkspace])
    have frameKept := node_new_branch_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeConstructorWorkspace])
    rw [run] at metadata scratchKept frameKept
    exact ⟨metadata.1.trans code,scratchKept.trans scratchGlobal,frameKept.trans frameGlobal⟩
  exact RunBounded.ofReaches budget reached (by
    intro next facts ticks
    rw [source_decode_step_branch_record]
    exact evaluate_scratch_alloc_decCall_straight_bounded next (.const 88) scratch 88 frame (ofString "rec2") .one
      decodeStepBranchStores
      (by simp only [decodeStepBranchStores,decodeStepBranchRecord,decodeStepBranchConstruction,sourceFunctionBody,
          InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)
      (by rw [evalListHOLFinite_eq_toExact]; rfl) facts.2.1 facts.2.2 facts.1 ticks)

theorem runBounded_decode_step_seventeen {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array scratch frame : BitVec 64)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word (17#64))]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (budget : 43 ≤ s.clock) :
    RunBounded s (decodeStepAt 6) 43 := by
  unfold RunBounded
  rw [evaluate_decode_step_seventeen s array atSlices]
  exact runBounded_decode_step_branch_construction s scratch frame scratchGlobal frameGlobal code budget

theorem decode_step_seventeen_returned_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (array scratch frame : BitVec 64) (value : ValueHOL 64)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word (17#64))]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch) (budget : 43 ≤ s.clock)
    (run : evaluateHOLFiniteState s (decodeStepAt 6) = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd scratch 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd scratch 88).toNat ∧
      (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat := by
  rw [evaluate_decode_step_seventeen s array atSlices] at run
  exact decode_step_branch_construction_uniform_returned_progress s post scratch frame value code budget
    scratchGlobal frameGlobal ordered run

#print axioms runBounded_decode_step_seventeen
#print axioms decode_step_seventeen_returned_progress
#print axioms runBounded_decode_step_branch_construction
end InitECandidate.Runtime
