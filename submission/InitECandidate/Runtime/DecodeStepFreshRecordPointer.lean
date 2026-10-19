import InitECandidate.Runtime.DecodeStepExtensionScratchProgress
import InitECandidate.Runtime.StoreChainReturnedPairLocal
import InitECandidate.Runtime.DecodeStepBranchScratchProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem scratch_parser_declaration_returned_pointer {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer frame tag : BitVec 64) (name : MlS) (tail : ProgHOL 64) (value : ValueHOL 64)
    (supported : StoreChainReturnedPairLocal name tag tail)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ pointer) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc") [.const 88] tail) =
      (some (.returned value),post)) :
    value = .rStruct [.val (.word tag),.val (.word (scratchAllocationEnd pointer 88))] := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "n",.val (.word (88#64)))
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 88] =
      some [.val (.word (88#64))] := by rw [evalListHOLFinite_eq_toExact]; rfl
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "scratch_alloc") [.val (.word (88#64))] =
      some (sourceFunctionBody Guest.guestFn_scratch_alloc,callee,.one) := by
    rw [code]
    exact pan_single_word_lookup _ _ _ _ 88 originalRuntimeCode_scratchAllocation_lookup
  obtain ⟨allocated,bodyPost,output,bodyRun,_,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post name (ofString "scratch_alloc") .one .one _ _
      (sourceFunctionBody Guest.guestFn_scratch_alloc) tail callee value args lookup run
  have progress := scratch_allocation_returned_progress (callEntryStateHOLFinite s callee) bodyPost pointer 88 frame
    allocated scratchGlobal
    (by simp [callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]) frameGlobal ordered code
    (by change 1 ≤ s.clock - 1; omega) bodyRun
  rw [progress.1] at tailRun
  exact evaluate_storeChain_returned_pair_local supported _ output (scratchAllocationEnd pointer 88) value
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) tailRun

/-- The actual extension path returns the freshly allocated scratch pointer,
not an arbitrary record with the same push flag. -/
theorem decode_step_extension_record_returned_pointer {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer frame : BitVec 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ pointer) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepExtensionRecord = (some (.returned value),post)) :
    value = .rStruct [.val (.word (1 : BitVec 64)),.val (.word (scratchAllocationEnd pointer 88))] := by
  rw [source_decodeStep_extension_record] at run
  apply scratch_parser_declaration_returned_pointer s post pointer frame 1 (ofString "rec") decodeStepExtensionStores
    value _ scratchGlobal frameGlobal ordered code ticks run
  rw [source_decodeStep_extension_stores]
  exact .store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ .finish)))))

theorem decode_step_branch_record_returned_pointer {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer frame : BitVec 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ pointer) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepBranchRecord = (some (.returned value),post)) :
    value = .rStruct [.val (.word (1 : BitVec 64)),.val (.word (scratchAllocationEnd pointer 88))] := by
  rw [source_decode_step_branch_record] at run
  apply scratch_parser_declaration_returned_pointer s post pointer frame 1 (ofString "rec2") decodeStepBranchStores
    value _ scratchGlobal frameGlobal ordered code ticks run
  simp only [decodeStepBranchStores,decodeStepBranchRecord,decodeStepBranchConstruction,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  exact .store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ .finish))))))

#print axioms decode_step_branch_record_returned_pointer
#print axioms scratch_parser_declaration_returned_pointer
#print axioms decode_step_extension_record_returned_pointer
end InitECandidate.Runtime
