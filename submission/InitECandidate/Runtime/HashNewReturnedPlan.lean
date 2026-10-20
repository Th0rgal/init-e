import InitECandidate.Runtime.HashNewBodyAllRequests
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual successful constructor execution proves every allocation in its
real plan fits. There is no extra space reserve or assumed callee contract. -/
theorem htabNew_returned_allocation_plan {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domains : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer → ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (wordDomain : AllocationPlanSafe pointer [72,capacity * allocationEnd 0 keyLength,capacity * 8,capacity] → ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (htabNewUsed pointer keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : AllocationPlanSafe pointer [72,capacity * allocationEnd 0 keyLength,capacity * 8,capacity] → ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL (htabNewUsed pointer keyLength capacity + BitVec.ofNat 64 offset)))
    (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)=(some (.returned value),post)) :
    AllocationPlanSafe pointer (htabNewAllocationSizes keyLength capacity) := by
  let output := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)
  have impossible (failure : ∀ v, output.1≠some (.returned v)) :
      AllocationPlanSafe pointer (htabNewAllocationSizes keyLength capacity) := by
    exact False.elim (failure value (congrArg Prod.fst run))
  have exactFailure (steps : Nat) (_stepsBound : steps≤capacity.toNat+8)
      (failure : output.1≠none ∧ output.1≠some .timeOut ∧
        (∀ v,output.1≠some (.returned v)) ∧output.2.clock=state.clock-steps) :
      AllocationPlanSafe pointer (htabNewAllocationSizes keyLength capacity) := impossible failure.2.2.1
  have rejection (p size : BitVec 64) (notLe : ¬size ≤ (33806089496 : BitVec 64) - p) :
      ((33806089496 : BitVec 64) - p).toNat < size.toNat := by
    have notNat : ¬size.toNat ≤ ((33806089496 : BitVec 64) - p).toNat := fun le => notLe (BitVec.le_def.mpr le)
    omega
  let keys := allocationEnd pointer 72
  let values := allocationEnd keys (capacity * allocationEnd 0 keyLength)
  let used := allocationEnd values (capacity * 8)
  let order := allocationEnd used capacity
  let reverse := allocationEnd order (capacity * 8)
  by_cases headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer
  · have headerFinish := allocationEnd_within_heap pointer 72 pointerBound headerRequest
    have domains := domains headerRequest
    have prefixDomains : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
      intro offset member
      apply domains offset
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have valueDomains : ∀ offset ∈ ([0,8,16,24,32] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset) := by
      intro offset member
      apply domains offset
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp
    by_cases keysRequest : capacity * allocationEnd 0 keyLength ≤ (33806089496 : BitVec 64) - keys
    · have keysFinish := allocationEnd_within_heap keys _ headerFinish keysRequest
      by_cases valuesRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - values
      · have valuesFinish := allocationEnd_within_heap values _ keysFinish valuesRequest
        by_cases usedRequest : capacity ≤ (33806089496 : BitVec 64) - used
        · have usedFinish := allocationEnd_within_heap used _ valuesFinish usedRequest
          have safePrefix : AllocationPlanSafe pointer [72,capacity * allocationEnd 0 keyLength,capacity * 8,capacity] :=
            ⟨headerRequest,headerFinish,keysRequest,keysFinish,valuesRequest,valuesFinish,usedRequest,usedFinish,usedFinish⟩
          have wordDomain := wordDomain safePrefix
          have byteDomain := byteDomain safePrefix
          by_cases orderRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - order
          · have orderFinish := allocationEnd_within_heap order _ usedFinish orderRequest
            by_cases reverseRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - reverse
            · have reverseFinish := allocationEnd_within_heap reverse _ orderFinish reverseRequest
              exact ⟨headerRequest,headerFinish,keysRequest,keysFinish,valuesRequest,valuesFinish,
                usedRequest,usedFinish,orderRequest,orderFinish,reverseRequest,reverseFinish,reverseFinish⟩
            · have failure := evaluate_htabNew_body_reverse_failure state pointer keyLength capacity code ticks heap
                headerRequest headerFinish keysRequest keysFinish keyLocal capLocal prefixDomains
                valuesRequest valuesFinish usedRequest usedFinish (domains 48 (by simp)) wordDomain byteDomain
                orderRequest orderFinish (domains 56 (by simp)) (rejection reverse _ reverseRequest)
              exact impossible failure.2.2.1
          · have failure := evaluate_htabNew_body_order_failure state pointer keyLength capacity code (by omega) heap
              headerRequest headerFinish keysRequest keysFinish keyLocal capLocal prefixDomains
              valuesRequest valuesFinish usedRequest usedFinish (domains 48 (by simp)) wordDomain byteDomain
              (rejection order _ orderRequest)
            exact impossible failure.2.2.1
        · apply exactFailure 5 (by omega)
          exact evaluate_htabNew_body_used_failure state pointer keyLength capacity code (by omega) heap
            headerRequest headerFinish keysRequest keysFinish keyLocal capLocal prefixDomains
            valuesRequest valuesFinish (rejection used _ usedRequest)
      · apply exactFailure 4 (by omega)
        exact evaluate_htabNew_body_values_failure state pointer keyLength capacity code (by omega) heap
          headerRequest headerFinish keysRequest keysFinish keyLocal capLocal valueDomains (rejection values _ valuesRequest)
    · apply exactFailure 3 (by omega)
      exact evaluate_htabNew_body_keys_failure state pointer keyLength capacity code (by omega) heap headerRequest headerFinish
        keyLocal capLocal (domains 0 (by simp)) (domains 8 (by simp)) (domains 16 (by simp)) (domains 24 (by simp))
        (rejection keys _ keysRequest)
  · apply exactFailure 2 (by omega)
    exact evaluate_htabNew_header_allocation_failure state pointer code heap (rejection pointer _ headerRequest) (by omega)

#print axioms htabNew_returned_allocation_plan
end InitECandidate.Runtime
