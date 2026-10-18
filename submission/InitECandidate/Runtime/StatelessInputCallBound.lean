import InitECandidate.Runtime.StatelessInputBodyBound
import InitECandidate.Runtime.OriginalDecodeStatelessInputCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original stateless-input call, including entry, uses at most
2*floor(inputLength/4)+inputLength+545 clocks, including every decoder rejection. -/
theorem evaluate_stateless_input_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer length offsets heapPointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (budget : statelessInputBound length + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "decode_stateless_input") arguments)
    state.clock ≤ evaluated.2.clock + (statelessInputBound length + 1) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "len",.val (.word length))
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_stateless_input_body_bounded entry pointer length heapPointer offsets p len atOffsets heap
    pointerBound aligned scratchBelow inputFits domain0 domain8 domain16 domain24 heapArena code (by change statelessInputBound length ≤ state.clock - 1; omega)
  have lookup := pan_two_word_lookup state.code.lookup (ofString "decode_stateless_input") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_stateless_input) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeStatelessInput_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_stateless_input) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have output := evaluate_call_body_clock_no_timeout state post (ofString "decode_stateless_input") destination arguments _
      (sourceFunctionBody Guest.guestFn_decode_stateless_input) callee .one result args lookup (by omega) bodyRun bounded.2.2
    dsimp only
    rw [output.2]
    refine ⟨?_,?_,output.1⟩
    · have consumed := bounded.1
      change state.clock - 1 ≤ post.clock + (statelessInputBound length) at consumed
      change state.clock ≤ post.clock + (statelessInputBound length + 1)
      omega
    · have remaining := bounded.2.1
      change post.clock ≤ state.clock - 1 at remaining
      change post.clock ≤ state.clock
      omega

#print axioms evaluate_stateless_input_call_bounded
end InitECandidate.Runtime
