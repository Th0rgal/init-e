import InitECandidate.Runtime.AllocationSuccess
import InitECandidate.Runtime.OriginalAllocationCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original alloc call and declaration-call entry: one clock updates the heap
pointer, preserves memory, restores caller locals, and binds the returned pointer
for the caller's actual continuation. -/
theorem evaluate_alloc_call_and_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer size : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer size).toNat ≤ 33806089496) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "alloc") [argument]) = (none,ready) ∧
      ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧ ready.locals = state.locals ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.eshapes = state.eshapes ∧ ready.be = state.be ∧
      ready.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd pointer size))) state).globals ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "alloc") [argument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) ready) continuation;
            (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
              (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,heap,ticks,memory,postCode,domain,shapes,endian,globals⟩ :=
    evaluate_source_alloc_success entry pointer size heapGlobal sizeLocal request finishBound
  have installed : state.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) size installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "alloc")
    [argument] [.val (.word size)] (sourceFunctionBody Guest.guestFn_alloc) callee .one (.val (.word pointer)) post
    arguments lookup clock body shapeOk
  refine ⟨{post with locals := state.locals},call,ticks,memory,rfl,postCode,domain,shapes,endian,globals,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state post name (ofString "alloc") .one .one [argument]
    [.val (.word size)] (sourceFunctionBody Guest.guestFn_alloc) continuation callee (.val (.word pointer))
    arguments lookup clock body (Nat.le_of_eq ticks) shapeOk shapeOk

#print axioms evaluate_alloc_call_and_declaration
end InitECandidate.Runtime
