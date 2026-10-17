import InitECandidate.Runtime.HashNewBodyAllRequests
import InitECandidate.Runtime.CallBodyClockNoTimeout
import InitECandidate.Runtime.OriginalHashNewCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual handler-free htab_new call, with any destination and any
64-bit arguments, finishes within capacity+9 source clocks. Heap exhaustion
is included. The required header and occupancy domains are explicit. -/
theorem evaluate_htabNew_call_all_requests {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer keyLength capacity : BitVec 64)
    (destination : Option (VarKind × MlS)) (keyArgument capacityArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [keyArgument,capacityArgument] = some [.val (.word keyLength),.val (.word capacity)])
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 9 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (domains : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer → ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (wordDomain : AllocationPlanSafe pointer [72,capacity * allocationEnd 0 keyLength,capacity * 8,capacity] → ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (htabNewUsed pointer keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : AllocationPlanSafe pointer [72,capacity * allocationEnd 0 keyLength,capacity * 8,capacity] → ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL (htabNewUsed pointer keyLength capacity + BitVec.ofNat 64 offset))) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "htab_new") [keyArgument,capacityArgument]);
    output.1 ≠ some .timeOut ∧
      state.clock ≤ output.2.clock + capacity.toNat + 9 ∧ output.2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))
  let entry := callEntryStateHOLFinite state callee
  let evaluated := evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_new)
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cap" ≠ ofString "key_len" from by decide]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bodyRun := evaluate_htabNew_body_all_requests entry pointer keyLength capacity code
    (by change capacity.toNat + 8 ≤ state.clock - 1; omega) heap pointerBound keyLocal capLocal domains wordDomain byteDomain
  have installed : state.code.lookup (ofString "htab_new") =
      some ([(ofString "key_len",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_htab_new,.one) := by
    rw [code]; exact originalRuntimeCode_htabNew_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new) keyLength capacity (by decide) installed
  have lifted := evaluate_call_body_clock_no_timeout state evaluated.2 (ofString "htab_new") destination
    [keyArgument,capacityArgument] [.val (.word keyLength),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) callee .one evaluated.1 arguments lookup (by omega) rfl bodyRun.2.1
  dsimp only at lifted ⊢
  refine ⟨lifted.1,?_,?_⟩
  · rw [lifted.2]
    have cost := bodyRun.2.2.1
    change state.clock - 1 ≤ evaluated.2.clock + capacity.toNat + 8 at cost
    omega
  · rw [lifted.2]
    have remaining := bodyRun.2.2.2
    change evaluated.2.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_htabNew_call_all_requests
end InitECandidate.Runtime
