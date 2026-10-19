import InitECandidate.Runtime.DecodeStepBranchConstructionProgress
import InitECandidate.Runtime.NodeNewBranchUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual branch construction consumes 88 scratch bytes on every returned
run, with no heap-room, heap-alignment or memory-domain assumption. -/
theorem decode_step_branch_construction_uniform_returned_progress {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (scratch frame : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode) (ticks : 43 ≤ state.clock)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch)
    (run : evaluateHOLFiniteState state decodeStepBranchConstruction = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd scratch 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd scratch 88).toNat ∧
      (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat := by
  let entry := callEntryStateHOLFinite state (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 64))
  have lookup := pan_no_args_lookup state.code.lookup (ofString "node_new_branch")
    (sourceFunctionBody Guest.guestFn_node_new_branch)
    (by rw [code]; exact originalRuntimeCode_nodeNewBranch_lookup)
  rw [source_decode_step_branch_construction] at run
  obtain ⟨allocated,bodyPost,output,bodyRun,_,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope state post (ofString "br") (ofString "node_new_branch") .one .one [] []
      (sourceFunctionBody Guest.guestFn_node_new_branch) decodeStepBranchRecord HolFiniteMapExact.empty value rfl lookup run
  have bound := runBounded_node_new_branch_body entry code (by change 40 ≤ state.clock - 1; omega)
  unfold RunBounded at bound
  rw [bodyRun] at bound
  have scratchKept := node_new_branch_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeConstructorWorkspace])
  have frameKept := node_new_branch_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeConstructorWorkspace])
  have metadata :=  evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_node_new_branch)
  rw [bodyRun] at scratchKept frameKept metadata
  have result := decode_step_branch_record_returned_progress
    (setVarHOLFinite (ofString "br") allocated {bodyPost with locals := state.locals}) output scratch frame value
    (scratchKept.trans scratchGlobal) (frameKept.trans frameGlobal) ordered (metadata.1.trans code)
    (by change 2 ≤ bodyPost.clock; have spent := bound.1; change state.clock - 1 ≤ bodyPost.clock + 40 at spent; omega)
    tailRun
  rw [postEq]
  exact result


#print axioms decode_step_branch_construction_uniform_returned_progress
end InitECandidate.Runtime
