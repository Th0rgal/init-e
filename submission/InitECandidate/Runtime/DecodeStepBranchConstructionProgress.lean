import InitECandidate.Runtime.DecodeStepBranchScratchProgress
import InitECandidate.Runtime.NodeConstructorWorkspaceFrame
import InitECandidate.Runtime.NodeNewBranchBody
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original heap constructor followed by its scratch record consumes 88
scratch bytes on the actual returned run. The heap-room premises permit the
existing successful constructor contract to supply its concrete clock bound. -/
theorem decode_step_branch_construction_returned_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer scratch frame : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 181 ≤ state.clock)
    (request : (176 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 176).toNat ≤ 33806089496)
    (bounded : pointer.toNat + 176 ≤ 33806089496) (aligned : pointer.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
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
  obtain ⟨constructorPost,constructorRun,cost,_,_⟩ := evaluate_nodeNewBranch_body entry pointer heap code
    (by change 178 ≤ state.clock - 1; omega) request finishBound bounded aligned wordDomain byteDomain
  rw [bodyRun] at constructorRun
  have samePost : bodyPost = constructorPost := (Prod.mk.inj constructorRun).2
  have scratchKept := node_new_branch_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeConstructorWorkspace])
  have frameKept := node_new_branch_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeConstructorWorkspace])
  have metadata :=  evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_node_new_branch)
  rw [bodyRun] at scratchKept frameKept metadata
  have result := decode_step_branch_record_returned_progress
    (setVarHOLFinite (ofString "br") allocated {bodyPost with locals := state.locals}) output scratch frame value
    (scratchKept.trans scratchGlobal) (frameKept.trans frameGlobal) ordered (metadata.1.trans code)
    (by change 2 ≤ bodyPost.clock; rw [samePost]; change state.clock - 1 ≤ constructorPost.clock + 178 at cost; omega)
    tailRun
  rw [postEq]
  exact result

#print axioms decode_step_branch_construction_returned_progress
end InitECandidate.Runtime
