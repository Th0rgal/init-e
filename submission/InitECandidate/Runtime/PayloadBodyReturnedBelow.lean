import InitECandidate.Runtime.PayloadBodyReturnedHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual decode_payload body keeps every word strictly below its entry
heap pointer outside the four scratch offset cells, on every return. -/
theorem payload_body_returned_below {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer w : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (header0 : state.memaddrs (heapPointer + 0)) (header8 : state.memaddrs (heapPointer + 8))
    (header16 : state.memaddrs (heapPointer + 16)) (header24 : state.memaddrs (heapPointer + 24))
    (header32 : state.memaddrs (heapPointer + 32)) (header40 : state.memaddrs (heapPointer + 40))
    (below : w.toNat < heapPointer.toNat)
    (sepOffsets : w ≠ offsets ∧ w ≠ offsets + 8 ∧ w ≠ offsets + 16 ∧ w ≠ offsets + 24)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload) = (some (.returned value),post)) :
    post.memory w = state.memory w := by
  obtain ⟨_,allocationRun⟩ := payload_body_returned_allocation_entry state post length value atLength code run
  have capacity := (payload_body_returned_allocation_capacity state post length heapPointer value atLength code heap heapBound run).2
  have nonzero : state.clock ≠ 0 := by
    rw [source_payload_allocation] at allocationRun
    exact evaluate_decCall_returned_nonzero_clock state post (ofString "pl") (ofString "alloc") .one
      [.const 136] (payloadAt 2) value allocationRun
  obtain ⟨ready,_,rmem,rdom,rcode,_,_,atPayload,locals,rglobals,_,allocation⟩ :=
    payload_allocation_success_entry state heapPointer code heap capacity aligned nonzero
  generalize hentry : payloadInputHeaderPost ready heapPointer pointer length = entry
  have stores := evaluate_payload_input_header_writes ready heapPointer pointer length atPayload
    ((locals _ (by decide)).trans atPointer) ((locals _ (by decide)).trans atLength)
    (by rw [rdom]; exact header0) (by rw [rdom]; exact header8)
  have continued : evaluateHOLFiniteState ready (payloadAt 2) = evaluateHOLFiniteState entry (payloadAt 4) := by
    rw [source_payload_input_header,← evaluate_seq_assoc]
    change evaluateHOLFiniteState ready (.seq payloadInputHeader (payloadAt 4)) = _
    rw [evaluateHOLFiniteState_seq_line780,stores, ← hentry]
  have endNat : (allocationEnd heapPointer 136).toNat = heapPointer.toNat + 136 :=
    allocationEnd_aligned_toNat heapPointer 136 capacity aligned (by decide)
  have hNat : ∀ c : BitVec 64, c.toNat ≤ 128 → (heapPointer + c).toNat = heapPointer.toNat + c.toNat := by
    intro c hc; rw [BitVec.toNat_add]; omega
  have neHeap : ∀ c : BitVec 64, c.toNat ≤ 128 → w ≠ heapPointer + c := by
    intro c hc e; have := congrArg BitVec.toNat e; rw [hNat c hc] at this; omega
  have entryMem : entry.memory w = state.memory w := by
    rw [← hentry]
    simp only [payloadInputHeaderPost, sourceWriteWord]
    rw [if_neg (neHeap 8 (by decide)), if_neg (neHeap 0 (by decide)), rmem]
  have entryOffsets : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
    rw [← hentry]; show ready.globals.lookup _ = _
    rw [rglobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atOffsets,
      show ofString "heap_ptr" ≠ ofString "ssz_offs" by decide]
  have entryHeap : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heapPointer 136))) := by
    rw [← hentry]; show ready.globals.lookup _ = _
    rw [rglobals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ed : entry.memaddrs = state.memaddrs := by rw [← hentry]; exact rdom
  have ec : entry.code = state.code := by rw [← hentry]; exact rcode
  have el : ∀ k, entry.locals.lookup k = ready.locals.lookup k := by intro k; rw [← hentry]; rfl
  rw [allocation, continued] at allocationRun
  cases tailRun : evaluateHOLFiniteState entry (payloadAt 4) with
  | mk result output =>
    rw [tailRun] at allocationRun
    dsimp only at allocationRun
    obtain ⟨r1, r2⟩ := Prod.mk.inj allocationRun
    subst r1
    have frame := payload_offset_header_frame entry output offsets length heapPointer pointer
      (allocationEnd heapPointer 136) w value entryOffsets ((el _).trans ((locals _ (by decide)).trans atLength))
      ((el _).trans atPayload) ((el _).trans ((locals _ (by decide)).trans atPointer)) entryHeap
      (by rw [endNat]; exact capacity)
      (by rw [ed]; exact domain0) (by rw [ed]; exact domain8) (by rw [ed]; exact domain16) (by rw [ed]; exact domain24)
      (by rw [ed]; exact header16) (by rw [ed]; exact header24) (by rw [ed]; exact header32) (by rw [ed]; exact header40)
      sepOffsets ⟨neHeap 16 (by decide), neHeap 24 (by decide)⟩
      (fun c hc => neHeap c (by simp at hc; rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide))
      (by rw [endNat]; omega) (ec.trans code) tailRun
    rw [← r2]
    show output.memory w = _
    rw [frame.1, entryMem]

#print axioms payload_body_returned_below
end InitECandidate.Runtime
