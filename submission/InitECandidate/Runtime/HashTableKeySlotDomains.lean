import InitECandidate.Runtime.HashTableArraysMemory
import InitECandidate.Runtime.HashFindArguments
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every byte of an in-range key has both source load domains at its actual width. -/
theorem HashTableArraysInvariant.key_slot_domains {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count slot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (inside : slot.toNat < capacity.toNat) :
    (keys + slot * stride).toNat % 8 = 0 ∧
      ∀ offset : Nat, offset < keyLength.toNat →
        state.memaddrs (keys + slot * stride + BitVec.ofNat 64 offset) ∧
        state.memaddrs (panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have keyBound : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496 := by omega
  refine ⟨(hashFind_slot_address keys slot stride capacity inside keyBound invariant.keysAligned invariant.strideAligned).2,?_⟩
  intro offset inRange
  have address := hashFind_slot_offset keys slot stride capacity keyLength offset inside keyBound invariant.keysAligned invariant.strideAligned invariant.fits inRange
  constructor
  · apply invariant.domain <;> omega
  · have align := invariant.keysAligned
    have division := Nat.mod_add_div keys.toNat 8
    have current := Nat.mod_add_div (keys + slot * stride + BitVec.ofNat 64 offset).toNat 8
    have remainder := Nat.mod_lt (keys + slot * stride + BitVec.ofNat 64 offset).toNat (by decide : 0 < 8)
    have natural := panByteAlign_toNat64 (keys + slot * stride + BitVec.ofNat 64 offset)
    apply invariant.domain <;> omega

#print axioms HashTableArraysInvariant.key_slot_domains
end InitECandidate.Runtime
