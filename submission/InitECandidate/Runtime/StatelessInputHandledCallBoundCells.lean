import InitECandidate.Runtime.StatelessInputHandledCallBound
import InitECandidate.Runtime.StatelessInputBodyBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem evaluate_stateless_input_handled_call_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (handlerId handlerVar : MlS) (handler : ProgHOL 64) (handlerCost : Nat)
    (pointer length offsets heapPointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (heapArena : ∀ address : BitVec 64, address.toNat % 8 = 0 → heapPointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (budget : statelessInputBound length + 1 + handlerCost ≤ state.clock)
    (handlerBound : ∀ (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite state (statelessInputCallee pointer length))
        (sourceFunctionBody Guest.guestFn_decode_stateless_input) = (some (.exception handlerId value),post) →
      handlerCost ≤ post.clock →
      let resumed := setVarHOLFinite handlerVar value {post with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed handler
      resumed.clock ≤ evaluated.2.clock + handlerCost ∧ evaluated.2.clock ≤ resumed.clock ∧
        evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state
      (.call (some (destination,some (handlerId,handlerVar,handler))) (ofString "decode_stateless_input") arguments)
    state.clock ≤ evaluated.2.clock + (statelessInputBound length + 1 + handlerCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := statelessInputCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,statelessInputCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,statelessInputCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_stateless_input_body_bounded_cells entry pointer length heapPointer offsets p len atOffsets heap
    heapBound aligned scratchBelow inputFits domain0 domain8 domain16 domain24 heapArena code
    (by change statelessInputBound length ≤ state.clock - 1; omega)
  have lookup := pan_two_word_lookup state.code.lookup (ofString "decode_stateless_input") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_stateless_input) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeStatelessInput_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_stateless_input) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have consumed : state.clock ≤ post.clock + (statelessInputBound length + 1) := by
      have spent := bounded.1
      change state.clock - 1 ≤ post.clock + statelessInputBound length at spent
      omega
    apply evaluate_handled_call_bounded state post (ofString "decode_stateless_input") handlerId handlerVar destination
      arguments [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_decode_stateless_input)
      handler callee .one result (statelessInputBound length + 1) handlerCost args lookup (by omega)
      bodyRun consumed (by have kept := bounded.2.1; change post.clock ≤ state.clock - 1 at kept; omega) bounded.2.2
    intro value exception
    exact handlerBound value post (by change evaluateHOLFiniteState entry _ = _; rw [bodyRun,exception]) (by omega)

#print axioms evaluate_stateless_input_handled_call_bounded_cells
end InitECandidate.Runtime
