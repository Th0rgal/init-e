import InitECandidate.Runtime.ScratchAllocationReturnedProgress
import InitECandidate.Runtime.DecodeStepExtensionRecord
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.OriginalScratchAllocationCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned parser-frame allocation followed by code that retains the scratch
global consumes 88 scratch bytes in the actual caller-visible final state. -/
theorem scratch_parser_declaration_returned_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer frame : BitVec 64) (name : MlS) (tail : ProgHOL 64) (value : ValueHOL 64)
    (keeps : avoidsGlobalAssignment (ofString "scratch_ptr") tail = true)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ pointer) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc") [.const 88] tail) =
      (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd pointer 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd pointer 88).toNat ∧
      (scratchAllocationEnd pointer 88).toNat + 88 ≤ pointer.toNat := by
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
  have kept := evaluate_avoidsGlobalAssignment (ofString "scratch_ptr") tail keeps
    (setVarHOLFinite name allocated {bodyPost with locals := s.locals})
  rw [tailRun] at kept
  refine ⟨?_,progress.2.2.1,progress.2.2.2.1⟩
  rw [postEq]
  exact kept.trans progress.2.1

/-- Returning from the original extension-record fragment, including its actual
stores, spends 88 scratch bytes. Malformed locals or inaccessible stores cannot
produce an unaccounted successful parser-frame return. -/
theorem decode_step_extension_record_returned_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer frame : BitVec 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ pointer) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepExtensionRecord = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd pointer 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd pointer 88).toNat ∧
      (scratchAllocationEnd pointer 88).toNat + 88 ≤ pointer.toNat := by
  rw [source_decodeStep_extension_record] at run
  exact scratch_parser_declaration_returned_progress s post pointer frame (ofString "rec")
    decodeStepExtensionStores value (by rw [source_decodeStep_extension_stores]; decide)
    scratchGlobal frameGlobal ordered code ticks run

#print axioms scratch_parser_declaration_returned_progress
#print axioms decode_step_extension_record_returned_progress
end InitECandidate.Runtime
