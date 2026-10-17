import InitECandidate.Runtime.HashNewCallAllRequests
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A full heap domain supplies only the cells the constructor actually
reaches. Failed requests require no domain facts beyond the heap limit. -/
theorem htabNew_requested_heap_domains {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer keyLength capacity : BitVec 64) (pointerBound : pointer.toNat ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    ((72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer →
      ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) ∧
    (AllocationPlanSafe pointer [72,capacity * allocationEnd 0 keyLength,capacity * 8,capacity] →
      (∀ offset : Nat, offset < capacity.toNat → state.memaddrs (htabNewUsed pointer keyLength capacity + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL (htabNewUsed pointer keyLength capacity + BitVec.ofNat 64 offset)))) := by
  refine ⟨?_,?_⟩
  · intro headerRequest offset member
    have headerBound := allocationGuard_sum_bound pointer 72 pointerBound headerRequest
    change pointer.toNat + 72 ≤ 33806089496 at headerBound
    have small : offset ≤ 64 := by simp at member; omega
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    exact heapDomain _ (by omega)
  · intro safe
    obtain ⟨_,_,_,keysFinish,valuesRequest,valuesFinish,usedRequest,_,_⟩ := safe
    have valuesBound := allocationGuard_sum_bound _ _ keysFinish valuesRequest
    have usedAligned := (allocationEnd_covers _ _ valuesBound).2.2
    have usedEnd := allocationGuard_sum_bound _ _ valuesFinish usedRequest
    change (htabNewUsed pointer keyLength capacity).toNat + capacity.toNat ≤ 33806089496 at usedEnd
    change (htabNewUsed pointer keyLength capacity).toNat % 8 = 0 at usedAligned
    have capacityBound := capacity.isLt
    refine ⟨?_,?_⟩
    · intro offset inside
      have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
      have address : (htabNewUsed pointer keyLength capacity + BitVec.ofNat 64 offset).toNat =
          (htabNewUsed pointer keyLength capacity).toNat + offset := by
        rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
      exact heapDomain _ (by omega)
    · intro offset inside
      have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
      have interval := hashOccupancy_aligned_interval (htabNewUsed pointer keyLength capacity) capacity (BitVec.ofNat 64 offset)
        usedAligned (by omega) (by rw [natural]; exact inside)
      exact heapDomain _ (by omega)

/-- With the challenge heap domain, every actual constructor call has a
capacity+9 bound even at heap exhaustion. No per-array or reserve premise is needed. -/
theorem evaluate_htabNew_call_heap_all_requests {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer keyLength capacity : BitVec 64)
    (destination : Option (VarKind × MlS)) (keyArgument capacityArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [keyArgument,capacityArgument] = some [.val (.word keyLength),.val (.word capacity)])
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 9 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "htab_new") [keyArgument,capacityArgument]);
    output.1 ≠ some .timeOut ∧
      state.clock ≤ output.2.clock + capacity.toNat + 9 ∧ output.2.clock ≤ state.clock := by
  have domains := htabNew_requested_heap_domains state pointer keyLength capacity pointerBound heapDomain
  exact evaluate_htabNew_call_all_requests state pointer keyLength capacity destination keyArgument capacityArgument
    arguments code ticks heap pointerBound domains.1 (fun safe => (domains.2 safe).1) (fun safe => (domains.2 safe).2)

#print axioms htabNew_requested_heap_domains
#print axioms evaluate_htabNew_call_heap_all_requests
end InitECandidate.Runtime
