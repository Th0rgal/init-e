import InitECandidate.Runtime.ScratchAllocationCallBound
import InitECandidate.Runtime.PanDecCallNormalReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the original allocator declaration-call certifies
both space checks and exposes its continuation with the exact allocated pointer. -/
theorem evaluate_scratch_alloc_decCall_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (argument : ExpHOL 64) (continuation : ProgHOL 64)
    (pointer size frame : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word size)])
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "scratch_alloc") [argument] continuation) = (none,post)) :
    size ≤ pointer - frame ∧ frame ≤ scratchAllocationEnd pointer size ∧
      ∃ ready output : PanSemStateFiniteExact 64 F, ready.locals = state.locals ∧
        evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (scratchAllocationEnd pointer size))) ready) continuation = (none,output) ∧
        post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,bodyPost,bodyRun,_,_,_,_,returned⟩ := evaluate_scratch_alloc_body_bounded entry pointer size frame
    scratchGlobal sizeLocal frameGlobal code (by change 1 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_scratchAllocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_scratch_alloc) size installed
  let property := fun value : ValueHOL 64 => value = .val (.word (scratchAllocationEnd pointer size)) ∧
    size ≤ pointer - frame ∧ frame ≤ scratchAllocationEnd pointer size
  have bodyProperty : ∀ value output, evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_scratch_alloc) =
      (some (.returned value),output) → property value := by
    intro value output evaluated
    exact returned value (Prod.mk.inj (bodyRun.symm.trans evaluated)).1
  obtain ⟨value,ready,output,valid,locals,tail,restored⟩ := evaluate_decCall_normal_return_property
    state post name (ofString "scratch_alloc") .one .one [argument] [.val (.word size)]
    (sourceFunctionBody Guest.guestFn_scratch_alloc) continuation callee args lookup property bodyProperty run
  obtain ⟨rfl,request,within⟩ := valid
  exact ⟨request,within,ready,output,locals,tail,restored⟩

#print axioms evaluate_scratch_alloc_decCall_normal
end InitECandidate.Runtime
