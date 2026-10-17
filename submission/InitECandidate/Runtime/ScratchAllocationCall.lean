import InitECandidate.Runtime.ScratchAllocationSuccess
import InitECandidate.Runtime.OriginalScratchAllocationCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original scratch allocator call and declaration-call entry: one clock updates the scratch
frontier, preserves memory, restores caller locals, and binds the returned pointer
for the caller's actual continuation. -/
theorem evaluate_scratch_alloc_call_and_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer size frame : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : size ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer size) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "scratch_alloc") [argument]) = (none,ready) ∧
      ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧ ready.locals = state.locals ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.eshapes = state.eshapes ∧ ready.be = state.be ∧
      ready.globals = (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word (scratchAllocationEnd pointer size))) state).globals ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "scratch_alloc") [argument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (scratchAllocationEnd pointer size))) ready) continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,heap,ticks,memory,postCode,domain,shapes,endian,globals⟩ :=
    evaluate_source_scratch_alloc_success entry pointer size frame scratchGlobal sizeLocal frameGlobal request finishBound
  have installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_scratchAllocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_scratch_alloc) size installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word (scratchAllocationEnd pointer size)))) .one = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "scratch_alloc")
    [argument] [.val (.word size)] (sourceFunctionBody Guest.guestFn_scratch_alloc) callee .one (.val (.word (scratchAllocationEnd pointer size))) post
    arguments lookup clock body shapeOk
  refine ⟨{post with locals := state.locals},call,ticks,memory,rfl,postCode,domain,shapes,endian,globals,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state post name (ofString "scratch_alloc") .one .one [argument]
    [.val (.word size)] (sourceFunctionBody Guest.guestFn_scratch_alloc) continuation callee (.val (.word (scratchAllocationEnd pointer size)))
    arguments lookup clock body (Nat.le_of_eq ticks) shapeOk shapeOk

#print axioms evaluate_scratch_alloc_call_and_declaration
end InitECandidate.Runtime
