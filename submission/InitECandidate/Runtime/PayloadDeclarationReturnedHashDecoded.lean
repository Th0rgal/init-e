import InitECandidate.Runtime.PayloadBodyReturnedHashDecoded
import InitECandidate.Runtime.HtrNewPayloadAllocationBound
import InitECandidate.Runtime.PayloadBodyReturnedValue
import InitECandidate.Runtime.OriginalDecodePayloadCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual payload declaration resumes its caller with the complete
hash metadata contract and the decoder's concrete heap geometry. -/
theorem payload_declaration_returned_hash_decoded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (arguments : List (ExpHOL 64))
    (pointer length offsets heapPointer : BitVec 64) (finalValue : ValueHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (small : length.toNat ≤ 134217712)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (header0 : state.memaddrs (heapPointer + 0)) (header8 : state.memaddrs (heapPointer + 8))
    (header16 : state.memaddrs (heapPointer + 16)) (header24 : state.memaddrs (heapPointer + 24))
    (header32 : state.memaddrs (heapPointer + 32)) (header40 : state.memaddrs (heapPointer + 40))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "decode_payload") arguments continuation) =
      (some (.returned finalValue),post)) :
    ∃ (array count nextHeap withdrawals balance extra : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState ready continuation = (some (.returned finalValue),output) ∧
      ready.locals = state.locals.update (name,.val (.word heapPointer)) ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      HtrPayloadDecoded ready heapPointer array count pointer length pointer length
        (pointer + withdrawals) ((balance - withdrawals) / 44) (pointer + balance) (length - balance)
        (pointer + 540) (extra - 540) ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      heapPointer.toNat + 136 ≤ nextHeap.toNat ∧ array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "len",.val (.word length))
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have lookup := pan_two_word_lookup state.code.lookup (ofString "decode_payload") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_payload) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodePayload_lookup)
  obtain ⟨value,bodyPost,output,bodyRun,checked,tail,restored⟩ := evaluate_decCall_checked_returned_exact_scope state post name
    (ofString "decode_payload") .one .one arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_decode_payload) continuation callee finalValue args lookup run
  have returned := payload_body_returned_value entry bodyPost pointer length offsets heapPointer value p len atOffsets heap
    heapBound aligned inputFits domain0 domain8 domain16 domain24 header0 header8 header16 header24 header32 header40 code bodyRun
  obtain ⟨array,count,nextHeap,withdrawals,balance,extra,decoded,nextGlobal,nextBound,nextAligned,growth,arrayBefore⟩ :=
    payload_body_returned_hash_decoded entry bodyPost pointer length offsets heapPointer value p len atOffsets heap
      heapBound aligned scratchBelow small inputFits domain0 domain8 domain16 domain24 header0 header8 header16 header24 header32 header40 code bodyRun
  rw [returned] at tail
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_payload)
  rw [bodyRun] at metadata
  let ready := setVarHOLFinite name (.val (.word heapPointer)) {bodyPost with locals := state.locals}
  refine ⟨array,count,nextHeap,withdrawals,balance,extra,ready,output,tail,rfl,metadata.1,metadata.2.1,
    decoded.after_frame rfl rfl,nextGlobal,nextBound,nextAligned,growth,arrayBefore,?_,?_,?_⟩
  all_goals rw [restored]

#print axioms payload_declaration_returned_hash_decoded
end InitECandidate.Runtime
