import InitECandidate.Runtime.AllocationFailureNoReturn
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.PanDecCallReturnedBodyScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned allocator declaration must have passed the actual request
guard: rejection invokes the trap and cannot return into the continuation. -/
theorem alloc_declaration_returned_request {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer size : BitVec 64) (name : MlS) (shape : ShapeHOL)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (run : evaluateHOLFiniteState state (.decCall name shape (ofString "alloc") [argument] continuation) =
      (some (.returned value),post)) :
    size ≤ (33806089496 : BitVec 64) - pointer := by
  by_contra rejected
  have tooBig : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat := by
    have bad : ¬ size.toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat := fun h => rejected (BitVec.le_def.mpr h)
    omega
  have installed : state.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) size installed
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  obtain ⟨returned,bodyPost,_,_,bodyRun,_⟩ := evaluate_decCall_returned_body_scope state post name (ofString "alloc") shape .one
    [argument] [.val (.word size)] (sourceFunctionBody Guest.guestFn_alloc) continuation callee value args lookup run
  have atSize : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,output,failure,_,noReturn,_⟩ := evaluate_source_alloc_request_failure_no_return entry pointer size code heap atSize tooBig
  have impossible := (Prod.mk.inj (failure.symm.trans bodyRun)).1
  exact noReturn returned impossible

#print axioms alloc_declaration_returned_request
end InitECandidate.Runtime
