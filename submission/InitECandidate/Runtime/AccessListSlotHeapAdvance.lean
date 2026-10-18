import InitECandidate.Runtime.AccessListKeysHeapAdvance
namespace InitECandidate.Runtime
open Flapjack

/-- An aligned slice array followed by its key buffer consumes exactly48 bytes
per slot, including both concrete source allocator roundings. -/
theorem access_slots_keys_heap_advance (pointer count : BitVec 64)
    (aligned : pointer.toNat % 8 = 0)
    (firstBound : pointer.toNat + count.toNat * 16 ≤ 33806089496)
    (secondBound : (allocationEnd pointer (count * 16)).toNat + count.toNat * 32 ≤ 33806089496) :
    (allocationEnd (allocationEnd pointer (count * 16)) (count * 32)).toNat =
      pointer.toNat + count.toNat * 48 := by
  have product : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have bound : pointer.toNat + (count * 16).toNat ≤ 33806089496 := by rw [product]; exact firstBound
  have firstNat := allocationEnd_aligned_toNat pointer (count * 16) bound aligned (by rw [product]; omega)
  rw [product] at firstNat
  have nextAligned := (allocationEnd_covers pointer (count * 16) bound).2.2
  rw [access_keys_heap_advance _ count nextAligned secondBound,firstNat]
  omega

#print axioms access_slots_keys_heap_advance
end InitECandidate.Runtime
