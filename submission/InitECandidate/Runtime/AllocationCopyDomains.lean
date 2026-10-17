import InitECandidate.Runtime.AllocationRound
namespace InitECandidate.Runtime
open Flapjack

/-- A successful request and full heap domain make every copied destination
byte and aligned containing word accessible, without further address premises. -/
theorem allocation_copy_domains {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer size : BitVec 64)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    (∀ offset : Nat, offset < size.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset)) ∧
    (∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) := by
  have bound := allocationGuard_sum_bound pointer size pointerBound request
  have addressBound : ∀ offset : Nat, offset < size.toNat → (pointer + BitVec.ofNat 64 offset).toNat < 33806089496 := by
    intro offset inside
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    omega
  constructor
  · intro offset inside
    exact heapDomain _ (addressBound offset inside)
  · intro offset inside
    apply heapDomain
    rw [panByteAlign_toNat64]
    have lower := Nat.div_mul_le_self (pointer + BitVec.ofNat 64 offset).toNat 8
    have upper := addressBound offset inside
    omega

#print axioms allocation_copy_domains
end InitECandidate.Runtime
