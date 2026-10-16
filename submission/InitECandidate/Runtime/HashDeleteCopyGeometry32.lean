import InitECandidate.Runtime.HashTableArraysRead32
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.HashFindArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Copying an in-range 32-byte key cannot overwrite later value or reverse
arrays. Key/value ordering is explicit because the general table invariant
only bounds each of those arrays against occupancy. -/
theorem HashTableArraysInvariant32.delete_copy_separate {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole scan : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) (scanInside : scan.toNat < capacity.toNat)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    ∀ watched ∈ ([values + scan * 8,orderPos + scan * 8] : List (BitVec 64)),
      ∀ offset : Nat, offset < 32 →
        watched ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
        watched ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset) := by
  have ku := invariant.keysBefore
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have limit := invariant.endBound
  have keyAddress := hashFind_slot_address keys hole stride capacity holeInside (by omega)
    invariant.keysAligned invariant.strideAligned
  have next : (hole.toNat + 1) * stride.toNat ≤ capacity.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat (by omega)
  rw [Nat.add_mul,Nat.one_mul] at next
  have fits := invariant.fits
  have copyEnd : (keys + hole * stride).toNat + 32 ≤ values.toNat := by
    rw [keyAddress.1]
    omega
  have valueAddress := (hashFind_slot_address values scan 8 capacity scanInside (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    invariant.valuesAligned (by decide)).1
  have reverseAddress := (hashFind_slot_address orderPos scan 8 capacity scanInside (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    invariant.orderPosAligned (by decide)).1
  change (values + scan * 8).toNat = values.toNat + scan.toNat * 8 at valueAddress
  change (orderPos + scan * 8).toNat = orderPos.toNat + scan.toNat * 8 at reverseAddress
  intro watched member offset inside
  have lower : values.toNat ≤ watched.toNat := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> omega
  exact memcpy_interval_separate (keys + hole * stride) 32 watched keyAddress.2
    (by change (keys + hole * stride).toNat + 32 ≤ 33806089496; omega)
    (Or.inr (by change (keys + hole * stride).toNat + 32 ≤ watched.toNat; omega))
    offset (by change offset < 32; exact inside)

#print axioms HashTableArraysInvariant32.delete_copy_separate
end InitECandidate.Runtime
