import InitECandidate.Runtime.HashNewBodyUsedPrefix
import InitECandidate.Runtime.HashNewZeroTailFailures
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The full original constructor handles order-array rejection after all
preceding allocations and occupancy clearing, within capacity+7 clocks. -/
theorem evaluate_htabNew_body_order_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer keyLength capacity : BitVec 64) (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 7 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerFinish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keysRequest : capacity * allocationEnd 0 keyLength ≤ (33806089496 : BitVec 64) - allocationEnd pointer 72)
    (keysFinish : (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)).toNat ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domains : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (valuesRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength))
    (valuesFinish : (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)).toNat ≤ 33806089496)
    (usedRequest : capacity ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8))
    (usedFinish : (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity).toNat ≤ 33806089496)
    (domain48 : state.memaddrs (pointer + 48))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs ((allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL ((allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) + BitVec.ofNat 64 offset)))
    (rejected : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity).toNat < (capacity * 8).toNat) :
    let output := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new);
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      state.clock ≤ output.2.clock + capacity.toNat + 7 ∧ output.2.clock ≤ state.clock := by
  obtain ⟨ready,resultEq,clockEq,clock,nextCode,domain,nextHeap,tableLocal,capAfter,usedLocal⟩ :=
    evaluate_htabNew_body_used_prefix state pointer keyLength capacity code (by omega) heap
      headerRequest headerFinish keysRequest keysFinish keyLocal capLocal domains valuesRequest valuesFinish usedRequest usedFinish
  have valuesBound := allocationGuard_sum_bound _ _ keysFinish valuesRequest
  have usedAligned := (allocationEnd_covers _ _ valuesBound).2.2
  have usedBound := allocationGuard_sum_bound _ _ valuesFinish usedRequest
  have failure := evaluate_htabNew_zero_then_order_failure ready _ pointer _ capacity (nextCode.trans code) (by omega)
    nextHeap usedBound usedAligned tableLocal usedLocal capAfter (by rw [domain]; exact domain48)
    (by simpa only [domain] using wordDomain) (by simpa only [domain] using byteDomain)
    rejected
  dsimp only at failure ⊢
  refine ⟨by rw [resultEq]; exact failure.1,by rw [resultEq]; exact failure.2.1,?_,?_,?_⟩
  · intro value
    rw [resultEq]; exact failure.2.2.1 value
  · rw [clockEq]
    have cost := failure.2.2.2.1
    omega
  · rw [clockEq]
    have remaining := failure.2.2.2.2
    omega

/-- The full original constructor handles reverse-array rejection after all
preceding allocations and occupancy clearing, within capacity+8 clocks. -/
theorem evaluate_htabNew_body_reverse_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer keyLength capacity : BitVec 64) (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerFinish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keysRequest : capacity * allocationEnd 0 keyLength ≤ (33806089496 : BitVec 64) - allocationEnd pointer 72)
    (keysFinish : (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)).toNat ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domains : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (valuesRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength))
    (valuesFinish : (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)).toNat ≤ 33806089496)
    (usedRequest : capacity ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8))
    (usedFinish : (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity).toNat ≤ 33806089496)
    (domain48 : state.memaddrs (pointer + 48))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs ((allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL ((allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) + BitVec.ofNat 64 offset)))
    (orderRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity)
    (orderFinish : (allocationEnd (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity) (capacity * 8)).toNat ≤ 33806089496)
    (domain56 : state.memaddrs (pointer + 56))
    (rejected : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity) (capacity * 8)).toNat < (capacity * 8).toNat) :
    let output := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new);
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      state.clock ≤ output.2.clock + capacity.toNat + 8 ∧ output.2.clock ≤ state.clock := by
  obtain ⟨ready,resultEq,clockEq,clock,nextCode,domain,nextHeap,tableLocal,capAfter,usedLocal⟩ :=
    evaluate_htabNew_body_used_prefix state pointer keyLength capacity code (by omega) heap
      headerRequest headerFinish keysRequest keysFinish keyLocal capLocal domains valuesRequest valuesFinish usedRequest usedFinish
  have valuesBound := allocationGuard_sum_bound _ _ keysFinish valuesRequest
  have usedAligned := (allocationEnd_covers _ _ valuesBound).2.2
  have usedBound := allocationGuard_sum_bound _ _ valuesFinish usedRequest
  have failure := evaluate_htabNew_zero_then_reverse_failure ready _ pointer _ capacity (nextCode.trans code) (by omega)
    nextHeap usedBound usedAligned tableLocal usedLocal capAfter (by rw [domain]; exact domain48)
    (by simpa only [domain] using wordDomain) (by simpa only [domain] using byteDomain)
    orderRequest orderFinish (by rw [domain]; exact domain56) rejected
  dsimp only at failure ⊢
  refine ⟨by rw [resultEq]; exact failure.1,by rw [resultEq]; exact failure.2.1,?_,?_,?_⟩
  · intro value
    rw [resultEq]; exact failure.2.2.1 value
  · rw [clockEq]
    have cost := failure.2.2.2.1
    omega
  · rw [clockEq]
    have remaining := failure.2.2.2.2
    omega

#print axioms evaluate_htabNew_body_order_failure
#print axioms evaluate_htabNew_body_reverse_failure
end InitECandidate.Runtime
