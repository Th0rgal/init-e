import InitECandidate.Runtime.AllocationFailureDeclaration
import InitECandidate.Runtime.AllocationFailureNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_alloc_request_failure_declaration_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer size : BitVec 64)
    (name : MlS) (shape : ShapeHOL) (continuation : ProgHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat)
    (clock : 2 ≤ state.clock) :
    (evaluateHOLFiniteState state (.decCall name shape (ofString "alloc") [argument] continuation)).1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have n : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,body,terminal,noReturn,noTimeout,ticks⟩ := evaluate_source_alloc_request_failure_no_timeout entry pointer size code heap n request (by change state.clock - 1 ≠ 0; omega)
  have installed : state.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) size installed
  rw [evaluateHOLFiniteState_decCall_total,arguments]
  dsimp only
  rw [lookup]
  dsimp only
  by_cases zero : state.clock = 0
  · omega
  · rw [if_neg zero,body]
    dsimp only
    change post.clock = state.clock - 1 - 1 at ticks
    cases result with
    | none => contradiction
    | some result =>
      cases result <;> simp_all [emptyLocalsHOLFinite,fixClockHOLFinite,entry,callEntryStateHOLFinite,Nat.sub_sub] <;> omega

#print axioms evaluate_alloc_request_failure_declaration_no_timeout
end InitECandidate.Runtime
