import InitECandidate.Runtime.PayloadBodyReturnedSlicesAbove
import InitECandidate.Runtime.PayloadBodyReturnedEntries
import InitECandidate.Runtime.PayloadBodyReturnedExtra
import InitECandidate.Runtime.PayloadBodyReturnedHeader
import InitECandidate.Runtime.HtrNewPayloadPayloadBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The concrete original decoder discharges every decoded-field premise of
the payload hash bound, including the actual transaction input slices. -/
theorem payload_body_returned_hash_decoded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
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
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload) = (some (.returned value),post)) :
    ∃ array count nextHeap withdrawals balance extra : BitVec 64,
      HtrPayloadDecoded post heapPointer array count pointer length pointer length
        (pointer + withdrawals) ((balance - withdrawals) / 44) (pointer + balance) (length - balance)
        (pointer + 540) (extra - 540) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      heapPointer.toNat + 136 ≤ nextHeap.toNat ∧ array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧
      (count = 0 ∨ heapPointer.toNat + 136 ≤ array.toNat) ∧ GlobalsExceptHeap state post := by
  obtain ⟨long,array,count,nextHeap,slices,countLimit,read32,read40,atHeap,cap,alignment,growth,arrayHeap,arrayOrigin⟩ :=
    payload_body_returned_slices_above state post pointer length offsets heapPointer value atPointer atLength atOffsets heap heapBound aligned inputFits domain0 domain8 domain16 domain24 header0 header8 header16 header24 header32 header40 code run
  obtain ⟨otherArray,otherCount,withdrawals,balance,ordered,inside,countBound,wdBound,requestBound,transactions,wdEntry,requestEntry⟩ :=
    payload_body_returned_entries state post pointer length offsets heapPointer value atPointer atLength atOffsets heap heapBound aligned small inputFits domain0 domain8 domain16 domain24 header0 header8 header16 header24 header32 header40 code run
  have pointerCell : post.memory (heapPointer + 32) = .word otherArray := transactions.pointerCell
  have lengthCell : post.memory (heapPointer + 40) = .word otherCount := by simpa [BitVec.add_assoc] using transactions.lengthCell
  have arrayEq : array = otherArray := by simpa using read32.symm.trans pointerCell
  have countEq : count = otherCount := by simpa using read40.symm.trans lengthCell
  subst otherArray
  subst otherCount
  obtain ⟨extra,extraBound,extraEntry⟩ := payload_body_returned_extra state post pointer length offsets heapPointer value atPointer atLength atOffsets heap heapBound aligned inputFits domain0 domain8 domain16 domain24 header0 header8 header16 header24 header32 header40 code run
  obtain ⟨rawPointer,rawLength,nonHeapGlobals⟩ := payload_body_returned_header state post pointer length offsets heapPointer value atPointer atLength atOffsets heap heapBound aligned scratchBelow
    domain0 domain8 domain16 domain24 header0 header8 header16 header24 header32 header40 code run
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_decode_payload)
  rw [run] at metadata
  have rawEntry : RlpSliceEntry post heapPointer 0 pointer length := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [metadata.2.1]; simpa using header0
    · rw [metadata.2.1]; simpa using header8
    · simpa using rawPointer
    · simpa using rawLength
  exact ⟨array,count,nextHeap,withdrawals,balance,extra,
    ⟨small,countBound,transactions,slices,rawEntry,wdEntry,wdBound,requestEntry,requestBound,extraEntry,(by omega)⟩,
    atHeap,cap,alignment,growth,arrayHeap,arrayOrigin,nonHeapGlobals⟩

#print axioms payload_body_returned_hash_decoded
end InitECandidate.Runtime
