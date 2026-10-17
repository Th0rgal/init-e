import InitECandidate.Runtime.HashTableArraysFindSupported
import InitECandidate.Runtime.HashGrowOldSlotDomainsWidth
import InitECandidate.Runtime.HashInsertCopyBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every key slot supplies aligned copy domains directly from the table allocation. -/
theorem HashTableArraysInvariant.key_slot_domains_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count slot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (inside : slot.toNat < capacity.toNat) :
    (keys + slot * stride).toNat % 8 = 0 ∧
      (∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (keys + slot * stride + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset))) ∧
      state.memaddrs (values + slot * 8) := by
  have hk := invariant.headerKeys
  have hv := invariant.headerValues
  have ku := invariant.keysBefore
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  apply hashGrow_old_slot_domains_width state keyLength keys stride values capacity slot inside
    invariant.keysAligned invariant.strideAligned invariant.valuesAligned invariant.fits (by omega) (by omega)
  · intro address lower upper
    apply invariant.domain <;> omega
  · intro address lower upper
    apply invariant.domain <;> omega

/-- Copying from the scanned slot to the deletion hole needs no extra
allocation or memory-domain assumptions. -/
theorem HashTableArraysInvariant.delete_copy_bounds_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count hole scan : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) (scanInside : scan.toNat < capacity.toNat) :
    HashInsertCopyBounds table keys stride (keys + scan * stride) keyLength used capacity hole state := by
  obtain ⟨aligned,words,bytes,_⟩ := invariant.key_slot_domains_width state keyLength table keys stride capacity used values order orderPos count scan bits scanInside
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  apply hashInsert_copy_bounds_from_array state table keys stride (keys + scan * stride) keyLength used capacity
    invariant.keysAligned invariant.strideAligned aligned invariant.usedAligned hk ku (by omega) invariant.fits
    ?_ words bytes hole holeInside
  intro address lower upper
  apply invariant.domain <;> omega

#print axioms HashTableArraysInvariant.key_slot_domains_width
#print axioms HashTableArraysInvariant.delete_copy_bounds_width
end InitECandidate.Runtime
