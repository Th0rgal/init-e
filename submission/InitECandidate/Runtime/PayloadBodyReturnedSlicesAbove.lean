import InitECandidate.Runtime.PayloadBodyReturnedSlices
import InitECandidate.Runtime.PayloadOffsetReturnedSlicesAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual return of the complete original payload decoder provides
input-bounded transaction slices, the concrete payload array/count header,
and an aligned capped heap beyond the array. Initial allocation capacity
is derived from the return itself, not assumed as a reserve. -/
theorem payload_body_returned_slices_above {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    540 ≤ length.toNat ∧ ∃ array count nextHeap : BitVec 64,
      RlpSliceInputPrefix post array pointer length count.toNat ∧ count.toNat ≤ length.toNat / 4 ∧
      post.memory (heapPointer + 32) = .word array ∧ post.memory (heapPointer + 40) = .word count ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      heapPointer.toNat + 136 ≤ nextHeap.toNat ∧ array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧
      (count = 0 ∨ heapPointer.toNat + 136 ≤ array.toNat) := by
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
    obtain ⟨array,count,nextHeap,inputPrefix,countBound,read32,read40,nextGlobal,nextBound,nextAligned,growth,arrayBefore,above⟩ :=
      payload_offset_returned_slices_above entry output offsets length heapPointer pointer (allocationEnd heapPointer 136) value
        entryOffsets len pl p entryHeap (by rw [endNat]; exact capacity) (by rw [endNat]; omega)
        (by rw [endNat]) inputFits
        (by rw [domain]; exact domain0) (by rw [domain]; exact domain8)
        (by rw [domain]; exact domain16) (by rw [domain]; exact domain24)
        (by rw [domain]; exact header16) (by rw [domain]; exact header24)
        (by rw [domain]; exact header32) (by rw [domain]; exact header40) (installed.trans code) tailRun
    have finalPrefix : RlpSliceInputPrefix post array pointer length count.toNat := by
      intro index inside
      obtain ⟨p,n,item⟩ := inputPrefix index inside
      exact ⟨p,n,item.after_frame output post array index p n pointer length postDomain
        (congrFun postMemory _) (congrFun postMemory _)⟩
    refine ⟨long,array,count,nextHeap,finalPrefix,countBound,?_,?_,?_,nextBound,nextAligned,?_,arrayBefore,above⟩
    · rw [postMemory]; exact read32
    · rw [postMemory]; exact read40
    · rw [postGlobals]; exact nextGlobal
    · rw [endNat] at growth
      exact growth

#print axioms payload_body_returned_slices_above
end InitECandidate.Runtime
