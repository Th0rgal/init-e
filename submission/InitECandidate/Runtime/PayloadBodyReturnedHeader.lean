import InitECandidate.Runtime.PayloadOffsetHeaderFrame
import InitECandidate.Runtime.PayloadBodyReturnedSlices
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual return of the complete original payload decoder keeps the
initial input header payload+0 = p and payload+8 = len (payload = entry
heap pointer) and every global other than heap_ptr, given the scratch
offset table lies below the payload. -/
theorem payload_body_returned_header {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (header0 : state.memaddrs (heapPointer + 0)) (header8 : state.memaddrs (heapPointer + 8))
    (header16 : state.memaddrs (heapPointer + 16)) (header24 : state.memaddrs (heapPointer + 24))
    (header32 : state.memaddrs (heapPointer + 32)) (header40 : state.memaddrs (heapPointer + 40))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload) = (some (.returned value),post)) :
    post.memory (heapPointer + 0) = .word pointer ∧ post.memory (heapPointer + 8) = .word length ∧
      GlobalsExceptHeap state post := by
  obtain ⟨_,allocationRun⟩ := payload_body_returned_allocation_entry state post length value atLength code run
  have capacity := (payload_body_returned_allocation_capacity state post length heapPointer value atLength code heap heapBound run).2
  have nonzero : state.clock ≠ 0 := by
    rw [source_payload_allocation] at allocationRun
    exact evaluate_decCall_returned_nonzero_clock state post (ofString "pl") (ofString "alloc") .one
      [.const 136] (payloadAt 2) value allocationRun
  obtain ⟨entry,_,domain,installed,pl,p,len,read0,read8,globals,declaration⟩ :=
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
    have h0 : (heapPointer + 0).toNat = heapPointer.toNat := by simp
    have h8 : (heapPointer + 8).toNat = heapPointer.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    have offNat : ∀ c : BitVec 64, c.toNat ≤ 24 → (offsets + c).toNat = offsets.toNat + c.toNat := by
      intro c hc; rw [BitVec.toNat_add]; omega
    have watched : ∀ w : BitVec 64, (w = heapPointer + 0 ∨ w = heapPointer + 8) →
        output.memory w = entry.memory w ∧ GlobalsExceptHeap entry output := by
      intro w hw
      have wNat : heapPointer.toNat ≤ w.toNat ∧ w.toNat ≤ heapPointer.toNat + 8 := by
        rcases hw with rfl | rfl <;> omega
      have neOff : ∀ c : BitVec 64, c.toNat ≤ 24 → w ≠ offsets + c := by
        intro c hc e; have := congrArg BitVec.toNat e; rw [offNat c hc] at this; omega
      have nePay : ∀ c : BitVec 64, c ∈ ([16,24,32,40,48,56,64,72,80,88,96,104,112,120,128] : List (BitVec 64)) →
          w ≠ heapPointer + c := by
        intro c hc e
        rcases hw with rfl | rfl <;> rw [BitVec.add_right_inj] at e <;> subst e <;> simp at hc
      refine payload_offset_header_frame entry output offsets length heapPointer pointer (allocationEnd heapPointer 136) w
        value entryOffsets len pl p entryHeap (by rw [endNat]; exact capacity)
        (by rw [domain]; exact domain0) (by rw [domain]; exact domain8)
        (by rw [domain]; exact domain16) (by rw [domain]; exact domain24)
        (by rw [domain]; exact header16) (by rw [domain]; exact header24)
        (by rw [domain]; exact header32) (by rw [domain]; exact header40)
        ⟨by simpa using neOff 0 (by decide), neOff 8 (by decide), neOff 16 (by decide), neOff 24 (by decide)⟩
        ⟨nePay 16 (by simp), nePay 24 (by simp)⟩ (fun c hc => nePay c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)))
        (by rw [endNat]; omega) (installed.trans code) tailRun
    obtain ⟨m0, g0⟩ := watched _ (Or.inl rfl)
    obtain ⟨m8, _⟩ := watched _ (Or.inr rfl)
    refine ⟨by rw [postMemory, m0]; exact read0, by rw [postMemory, m8]; exact read8, fun k hk => ?_⟩
    rw [postGlobals, g0 k hk, globals]
    simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]

#print axioms payload_body_returned_header
end InitECandidate.Runtime
