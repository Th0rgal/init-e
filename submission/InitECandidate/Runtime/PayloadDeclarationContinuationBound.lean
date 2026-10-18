import InitECandidate.Runtime.PayloadBodyInputBound
import InitECandidate.Runtime.PayloadBodyReturnedSlices
import InitECandidate.Runtime.PayloadBodyReturnedHeader
import InitECandidate.Runtime.OriginalDecodePayloadCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanDecCallContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original payload call transmits its capped heap and nonallocator
global frame to the continuation. All nonreturning outcomes retain the
input-length source-clock bound. -/
theorem evaluate_payload_declaration_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (tailCost : Nat) (arguments : List (ExpHOL 64))
    (pointer length offsets heapPointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode)
    (budget : sszSplitBound length + 80 + tailCost ≤ state.clock)
    (continuationBound : ∀ (value : ValueHOL 64) (ready : PanSemStateFiniteExact 64 F) (nextHeap : BitVec 64),
      ready.locals = state.locals.update (name,value) → ready.code = state.code → ready.memaddrs = state.memaddrs →
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) → nextHeap.toNat ≤ 33806089496 →
      (∀ key, key ≠ ofString "heap_ptr" → ready.globals.lookup key = state.globals.lookup key) →
      tailCost ≤ ready.clock →
      let evaluated := evaluateHOLFiniteState ready continuation
      ready.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ ready.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name .one (ofString "decode_payload") arguments continuation)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + 80 + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "len",.val (.word length))
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_payload_body_input_bounded entry pointer length offsets heapPointer p len atOffsets code
    heap heapBound aligned domain0 domain8 domain16 domain24 (by change sszSplitBound length + 79 ≤ state.clock - 1; omega)
  have lookup := pan_two_word_lookup state.code.lookup (ofString "decode_payload") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_payload) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodePayload_lookup)
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_payload)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_payload) with
  | mk result post =>
    rw [bodyRun] at bounded metadata
    dsimp only at bounded metadata
    have consumed : state.clock ≤ post.clock + (sszSplitBound length + 80) := by
      have spent := bounded.1
      change state.clock - 1 ≤ post.clock + (sszSplitBound length + 79) at spent
      omega
    apply evaluate_decCall_continuation_bounded state post name (ofString "decode_payload") .one .one arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_decode_payload)
      continuation callee result (sszSplitBound length + 80) tailCost args lookup (by omega) bodyRun
      bounded.2.1 consumed bounded.2.2
    intro value returned
    have returnedRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_payload) =
        (some (.returned value),post) := by rw [bodyRun,returned]
    have capacity := (payload_body_returned_allocation_capacity entry post length heapPointer value
      len code heap heapBound returnedRun).2
    have header : ∀ c : BitVec 64, c.toNat ≤ 40 → entry.memaddrs (heapPointer + c) := by
      intro c small
      have address : (heapPointer + c).toNat = heapPointer.toNat + c.toNat := by
        rw [BitVec.toNat_add]; omega
      exact heapArena _ (by rw [address]; omega) (by rw [address]; omega)
    have header0 := header 0 (by decide)
    have header8 := header 8 (by decide)
    have header16 := header 16 (by decide)
    have header24 := header 24 (by decide)
    have header32 := header 32 (by decide)
    have header40 := header 40 (by decide)
    obtain ⟨_,array,count,nextHeap,_,_,_,_,nextGlobal,nextBound,_,_,_⟩ :=
      payload_body_returned_slices entry post pointer length offsets heapPointer value p len atOffsets heap heapBound
        aligned inputFits domain0 domain8 domain16 domain24 header0 header8 header16 header24 header32 header40 code returnedRun
    have other := (payload_body_returned_header entry post pointer length offsets heapPointer value p len atOffsets heap
      heapBound aligned scratchBelow domain0 domain8 domain16 domain24 header0 header8 header16 header24 header32 header40
      code returnedRun).2.2
    let ready := setVarHOLFinite name value {post with locals := state.locals}
    exact continuationBound value ready nextHeap rfl metadata.1 metadata.2.1 nextGlobal nextBound other
      (by change tailCost ≤ post.clock; omega)

#print axioms evaluate_payload_declaration_continuation_bounded
end InitECandidate.Runtime
