import InitECandidate.Runtime.PayloadOffsetReturnedValue
import InitECandidate.Runtime.PayloadOffsetEntry
import InitECandidate.Runtime.PayloadReturnedAllocationCapacity
import InitECandidate.Runtime.PanDecCallReturnedNonzeroClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual return of the complete original payload decoder is the initial heap pointer allocated for the payload. Allocation capacity follows from the returned run. -/
theorem payload_body_returned_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (header0 : state.memaddrs (heapPointer + 0)) (header8 : state.memaddrs (heapPointer + 8))
    (header16 : state.memaddrs (heapPointer + 16)) (header24 : state.memaddrs (heapPointer + 24))
    (header32 : state.memaddrs (heapPointer + 32)) (header40 : state.memaddrs (heapPointer + 40))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload) = (some (.returned value),post)) :
    value = .val (.word heapPointer) := by
  obtain ⟨long,allocationRun⟩ := payload_body_returned_allocation_entry state post length value atLength code run
  have capacity := (payload_body_returned_allocation_capacity state post length heapPointer value atLength code heap heapBound run).2
  have nonzero : state.clock ≠ 0 := by
    rw [source_payload_allocation] at allocationRun
    exact evaluate_decCall_returned_nonzero_clock state post (ofString "pl") (ofString "alloc") .one
      [.const 136] (payloadAt 2) value allocationRun
  obtain ⟨entry,clock,domain,installed,pl,p,len,read0,read8,globals,declaration⟩ :=
    payload_offset_entry state heapPointer pointer length atPointer atLength code heap capacity aligned header0 header8 nonzero
  have endNat : (allocationEnd heapPointer 136).toNat = heapPointer.toNat + 136 :=
    allocationEnd_aligned_toNat heapPointer 136 capacity aligned (by decide)
  have entryOffsets : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atOffsets,
      show ofString "heap_ptr" ≠ ofString "ssz_offs" by decide]
  have entryHeap : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heapPointer 136))) := by
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [declaration] at allocationRun
  cases tailRun : evaluateHOLFiniteState entry (payloadAt 4) with
  | mk result output =>
    rw [tailRun] at allocationRun
    dsimp only at allocationRun
    have resultEq := (Prod.mk.inj allocationRun).1
    subst result
    have restored := (Prod.mk.inj allocationRun).2.symm
    have postMemory : post.memory = output.memory := by rw [restored]
    have postGlobals : post.globals = output.globals := by rw [restored]
    have postDomain : post.memaddrs = output.memaddrs := by rw [restored]
    exact payload_offset_returned_value entry output offsets length heapPointer pointer (allocationEnd heapPointer 136) value
        entryOffsets len pl p entryHeap (by rw [endNat]; exact capacity) (by rw [endNat]; omega)
        (by rw [endNat]) inputFits
        (by rw [domain]; exact domain0) (by rw [domain]; exact domain8)
        (by rw [domain]; exact domain16) (by rw [domain]; exact domain24)
        (by rw [domain]; exact header16) (by rw [domain]; exact header24)
        (by rw [domain]; exact header32) (by rw [domain]; exact header40) (installed.trans code) tailRun

#print axioms payload_body_returned_value
end InitECandidate.Runtime
