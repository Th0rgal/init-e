import InitECandidate.Runtime.DecodeBranchPlacement
import InitECandidate.Runtime.DecodeStepAllocatedRecordMetadata
import InitECandidate.Runtime.DecodeStepBranchReturnedHeap
import InitECandidate.Runtime.AllocationRoundNoWrap
import InitECandidate.Runtime.DecodeStepScratchRecordFrame
import InitECandidate.Runtime.NodeConstructorsReturnedHeap
import InitECandidate.Runtime.DecodeStepBranchUniformProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_branch_construction_returned_placement {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap scratch frame arr p n : BitVec 64)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat%8=0)
    (tableBefore : arr.toNat+272 ≤ heap.toNat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 43 ≤ s.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepBranchConstruction = (some (.returned value),post)) :
    DecoderBranchPlaced post (scratchAllocationEnd scratch 88) arr.toNat := by
  have allHeap := decode_step_branch_construction_returned_heap_contract s post heap scratch frame arr p n atHeap heapBound
    aligned atArray atPointer atLength scratchGlobal frameGlobal ordered code ticks value run
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 64))
  have lookup := pan_no_args_lookup s.code.lookup (ofString "node_new_branch")
    (sourceFunctionBody Guest.guestFn_node_new_branch)
    (by rw [code]; exact originalRuntimeCode_nodeNewBranch_lookup)
  rw [source_decode_step_branch_construction] at run
  obtain ⟨allocated,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "br") (ofString "node_new_branch") .one .one [] []
      (sourceFunctionBody Guest.guestFn_node_new_branch) decodeStepBranchRecord HolFiniteMapExact.empty value rfl lookup run
  obtain ⟨rfl,heapPost,growth,capped,finishAligned,memory⟩ := node_new_branch_body_returned_heap_contract
    entry bodyPost heap atHeap heapBound aligned code allocated bodyRun
  have bound := runBounded_node_new_branch_body entry code (by change 40 ≤ s.clock-1; omega)
  unfold RunBounded at bound
  rw [bodyRun] at bound
  have scratchKept := node_new_branch_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeConstructorWorkspace])
  have frameKept := node_new_branch_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeConstructorWorkspace])
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_node_new_branch)
  rw [bodyRun] at scratchKept frameKept metadata
  let ready := setVarHOLFinite (ofString "br") (.val (.word heap)) {bodyPost with locals := s.locals}
  have atBr : ready.locals.lookup (ofString "br") = some (.val (.word heap)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "br" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  obtain ⟨stage,branchCell,arrayCell,index,occupied,pointerCell,lengthCell⟩ := decode_step_branch_record_returned_metadata
    ready output scratch frame arr p n heap ((other _ (by decide)).trans atArray) ((other _ (by decide)).trans atPointer)
    ((other _ (by decide)).trans atLength) atBr (scratchKept.trans scratchGlobal) (frameKept.trans frameGlobal)
    ordered (metadata.1.trans code)
    (by change 2 ≤ bodyPost.clock; have spent := bound.1; change s.clock-1 ≤ bodyPost.clock+40 at spent; omega)
    value tailRun
  have covers : heap.toNat+176 ≤ (allocationEnd heap 176).toNat := by
    have actual := allocationEnd_covers_noWrap heap 176 (by change heap.toNat+176+7 < 2^64; omega)
    exact actual
  refine ⟨arr,heap,allocationEnd heap 176,?_,?_,by omega,tableBefore,covers,aligned,allHeap.1,allHeap.2.2.1⟩
  · rw [postEq]; exact arrayCell
  · rw [postEq]; exact branchCell

#print axioms decode_step_branch_construction_returned_placement
end InitECandidate.Runtime
