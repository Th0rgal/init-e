import InitECandidate.Runtime.HashTableArraysFind32
import InitECandidate.Runtime.HashGrowOldSlotDomains
import InitECandidate.Runtime.HashInsertCopyBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every key slot supplies aligned copy domains directly from the table allocation. -/
theorem HashTableArraysInvariant32.key_slot_domains {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count slot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (inside : slot.toNat < capacity.toNat) :
    (keys + slot * stride).toNat % 8 = 0 ∧
      (∀ offset : Nat, offset < 32 → state.memaddrs (keys + slot * stride + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset))) ∧
      state.memaddrs (values + slot * 8) := by
  have hk := invariant.headerKeys
  have hv := invariant.headerValues
  have ku := invariant.keysBefore
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  apply hashGrow_old_slot_domains state keys stride values capacity slot inside
    invariant.keysAligned invariant.strideAligned invariant.valuesAligned invariant.fits (by omega) (by omega)
  · intro address lower upper
    apply invariant.domain <;> omega
  · intro address lower upper
    apply invariant.domain <;> omega

/-- Copying from the scanned slot to the deletion hole needs no extra
allocation or memory-domain assumptions. -/
theorem HashTableArraysInvariant32.delete_copy_bounds {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole scan : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) (scanInside : scan.toNat < capacity.toNat) :
    HashInsertCopyBounds table keys stride (keys + scan * stride) 32 used capacity hole state := by
  obtain ⟨aligned,words,bytes,_⟩ := invariant.key_slot_domains state table keys stride capacity used values order orderPos count scan bits scanInside
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  apply hashInsert_copy_bounds_from_array state table keys stride (keys + scan * stride) 32 used capacity
    invariant.keysAligned invariant.strideAligned aligned invariant.usedAligned hk ku (by omega) invariant.fits
    ?_ words bytes hole holeInside
  intro address lower upper
  apply invariant.domain <;> omega

#print axioms HashTableArraysInvariant32.key_slot_domains
#print axioms HashTableArraysInvariant32.delete_copy_bounds
end InitECandidate.Runtime
