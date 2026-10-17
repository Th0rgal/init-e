import InitECandidate.Runtime.OriginalHeapControlCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_heapRelease_body : sourceFunctionBody Guest.guestFn_heap_release =
    .seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Releasing a saved mark changes only the heap global and the call clock.
Any registry preservation additionally needs its live allocations below the mark. -/
theorem evaluate_heapRelease_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (mark current : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word mark)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word current)))
    (ticks : state.clock ≠ 0) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "heap_release") [argument]) = (none,post) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mark)) state).globals ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "m",.val (.word mark))
  let entry := callEntryStateHOLFinite state callee
  have m : entry.locals.lookup (ofString "m") = some (.val (.word mark)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  let released := setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mark)) entry
  have assigned : evaluateHOLFiniteState entry (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) = (none,released) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,m,isValidValueHOLExact,lookupKvarHOLExact,
      show entry.globals.lookup (ofString "heap_ptr") = some (.val (.word current)) from heap,
      shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,released]
  have body : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_heap_release) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite released) := by
    rw [source_heapRelease_body,evaluateHOLFiniteState_seq_line780,assigned]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have installed : state.code.lookup (ofString "heap_release") = some ([(ofString "m",.one)],sourceFunctionBody Guest.guestFn_heap_release,.one) := by
    rw [code]
    exact originalRuntimeCode_heap_release_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "heap_release") (ofString "m")
    (sourceFunctionBody Guest.guestFn_heap_release) mark installed
  have shape : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "heap_release") [argument] [.val (.word mark)]
    (sourceFunctionBody Guest.guestFn_heap_release) callee .one (.val (.word (0 : BitVec 64))) (emptyLocalsHOLFinite released) args lookup ticks body shape
  exact ⟨_,call,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms source_heapRelease_body
#print axioms evaluate_heapRelease_call
end InitECandidate.Runtime
