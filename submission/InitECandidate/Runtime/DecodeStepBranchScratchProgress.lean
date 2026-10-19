import InitECandidate.Runtime.DecodeStepExtensionScratchProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original branch-node construction after the two-element case. -/
def decodeStepBranchConstruction : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn__decode_step with
  | .dec _ _ _ (.dec _ _ _ (.seq _ (.seq _ (.decCall _ _ _ _ (.dec _ _ _
      (.seq _ (.seq _ branch))))))) => branch
  | _ => .skip

def decodeStepBranchRecord : ProgHOL 64 :=
  match decodeStepBranchConstruction with | .decCall _ _ _ _ record => record | _ => .skip

def decodeStepBranchStores : ProgHOL 64 :=
  match decodeStepBranchRecord with | .decCall _ _ _ _ stores => stores | _ => .skip

theorem source_decode_step_branch_construction : decodeStepBranchConstruction =
    .decCall (ofString "br") .one (ofString "node_new_branch") [] decodeStepBranchRecord := by
  simp only [decodeStepBranchConstruction,decodeStepBranchRecord,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_decode_step_branch_record : decodeStepBranchRecord =
    .decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88] decodeStepBranchStores := by
  simp only [decodeStepBranchRecord,decodeStepBranchStores,decodeStepBranchConstruction,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem decode_step_branch_stores_keep_scratch :
    avoidsGlobalAssignment (ofString "scratch_ptr") decodeStepBranchStores = true := by
  unfold decodeStepBranchStores decodeStepBranchRecord decodeStepBranchConstruction sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  decide

/-- Every successful return of the original branch continuation-record fragment
consumes 88 scratch bytes, including the stores and its structured result. -/
theorem decode_step_branch_record_returned_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer frame : BitVec 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ pointer) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepBranchRecord = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd pointer 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd pointer 88).toNat ∧
      (scratchAllocationEnd pointer 88).toNat + 88 ≤ pointer.toNat := by
  rw [source_decode_step_branch_record] at run
  exact scratch_parser_declaration_returned_progress s post pointer frame (ofString "rec2")
    decodeStepBranchStores value decode_step_branch_stores_keep_scratch scratchGlobal frameGlobal ordered code ticks run

#print axioms source_decode_step_branch_construction
#print axioms source_decode_step_branch_record
#print axioms decode_step_branch_stores_keep_scratch
#print axioms decode_step_branch_record_returned_progress
end InitECandidate.Runtime
