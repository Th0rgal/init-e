import InitECandidate.Runtime.HashNewCallHeapAllRequests
import InitECandidate.Runtime.HashNewBodyUnsafeNoReturn
import InitECandidate.Runtime.CallNonreturnDestination
import InitECandidate.Runtime.DiscardCallTerminal
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A constructor whose allocation plan cannot fit exits exceptionally for every
call destination. It cannot continue as a successful constructor call. -/
theorem evaluate_htabNew_call_heap_unsafe_terminal {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer keyLength capacity : BitVec 64)
    (destination : Option (VarKind × MlS)) (keyArgument capacityArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [keyArgument,capacityArgument] = some [.val (.word keyLength),.val (.word capacity)])
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 9 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (planRejected : ¬AllocationPlanSafe pointer (htabNewAllocationSizes keyLength capacity)) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "htab_new") [keyArgument,capacityArgument]);
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      state.clock ≤ output.2.clock + capacity.toNat + 9 ∧ output.2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))
  let entry := callEntryStateHOLFinite state callee
  let evaluated := evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_new)
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cap" ≠ ofString "key_len" from by decide]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have domains := htabNew_requested_heap_domains state pointer keyLength capacity pointerBound heapDomain
  have bodyNoReturn := evaluate_htabNew_body_unsafe_no_return entry pointer keyLength capacity code
    (by change capacity.toNat + 8 ≤ state.clock - 1; omega) heap pointerBound keyLocal capLocal domains.1
    (fun safe => (domains.2 safe).1) (fun safe => (domains.2 safe).2) planRejected
  have installed : state.code.lookup (ofString "htab_new") =
      some ([(ofString "key_len",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_htab_new,.one) := by
    rw [code]; exact originalRuntimeCode_htabNew_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new) keyLength capacity (by decide) installed
  have equal := evaluate_call_nonreturn_destination state evaluated.2 (ofString "htab_new") destination
    [keyArgument,capacityArgument] [.val (.word keyLength),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) callee .one evaluated.1 arguments lookup (by omega) rfl bodyNoReturn
  have terminal := evaluate_discard_call_body_terminal state evaluated.2 (ofString "htab_new")
    [keyArgument,capacityArgument] [.val (.word keyLength),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) callee .one evaluated.1 arguments lookup (by omega) rfl bodyNoReturn
  have runtime := evaluate_htabNew_call_heap_all_requests state pointer keyLength capacity destination keyArgument capacityArgument
    arguments code ticks heap pointerBound heapDomain
  dsimp only at runtime ⊢
  refine ⟨?_,runtime.1,?_,runtime.2.1,runtime.2.2⟩
  · rw [equal]; exact terminal
  · intro value
    rw [equal]
    exact evaluate_discard_call_no_return state (ofString "htab_new") [keyArgument,capacityArgument] value

#print axioms evaluate_htabNew_call_heap_unsafe_terminal
end InitECandidate.Runtime
