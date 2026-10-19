import InitECandidate.Runtime.DecodeStepExtensionScratchProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Invert the actual scratch allocation and expose the exact record binding,
unchanged memory/heap and real lower-frontier bound for its continuation. -/
theorem scratch_parser_declaration_returned_environment {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame : BitVec 64)
    (name : MlS) (tail : ProgHOL 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc") [.const 88] tail) =
      (some (.returned value),post)) :
    ∃ ready output : PanSemStateFiniteExact 64 F,
      ready.locals = s.locals.update (name,.val (.word (scratchAllocationEnd scratch 88))) ∧
      ready.memory = s.memory ∧
      ready.globals.lookup (ofString "heap_ptr") = s.globals.lookup (ofString "heap_ptr") ∧
      ready.code = s.code ∧
      evaluateHOLFiniteState ready tail = (some (.returned value),output) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧
      (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "n",.val (.word (88#64)))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 88] =
      some [.val (.word (88#64))] := by rfl
  have lookup := pan_single_word_lookup s.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_scratch_alloc) 88
    (by rw [code]; exact originalRuntimeCode_scratchAllocation_lookup)
  obtain ⟨allocated,bodyPost,output,bodyRun,_,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post name (ofString "scratch_alloc") .one .one _ _
      (sourceFunctionBody Guest.guestFn_scratch_alloc) tail callee value args lookup run
  have atSize : entry.locals.lookup (ofString "n") = some (.val (.word (88#64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,computed,computedRun,_,_,_,_,returns⟩ := evaluate_scratch_alloc_body_bounded
    entry scratch 88 frame scratchGlobal atSize frameGlobal code (by change 1 ≤ s.clock-1; omega)
  have actualResult := (Prod.mk.inj (computedRun.symm.trans bodyRun)).1
  obtain ⟨rfl,request,within⟩ := returns allocated actualResult
  obtain ⟨actual,actualRun,_,_,memory,_,_,_,_,globals⟩ := evaluate_source_scratch_alloc_success
    entry scratch 88 frame scratchGlobal atSize frameGlobal request within
  have postSame := (Prod.mk.inj (bodyRun.symm.trans actualRun)).2
  have requested := BitVec.le_def.mp request
  rw [BitVec.toNat_sub_of_le ordered] at requested
  have fits : (88 : BitVec 64).toNat ≤ scratch.toNat := by
    change 88 ≤ scratch.toNat
    change 88 ≤ scratch.toNat - frame.toNat at requested
    omega
  have recordBefore := scratchAllocationEnd_before scratch 88 fits
  let ready := setVarHOLFinite name (.val (.word (scratchAllocationEnd scratch 88))) {bodyPost with locals := s.locals}
  refine ⟨ready,output,rfl,?_,?_,?_,tailRun,?_,?_,?_⟩
  · change bodyPost.memory = s.memory
    rw [postSame,memory]
    rfl
  · change bodyPost.globals.lookup _ = _
    rw [postSame,globals]
    simp [setGlobalHOLFinite,entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
  · have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_scratch_alloc)
    rw [bodyRun] at metadata
    exact metadata.1
  · rw [postEq]
  · rw [postEq]
  · exact recordBefore

#print axioms scratch_parser_declaration_returned_environment
end InitECandidate.Runtime
