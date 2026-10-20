import InitECandidate.Runtime.ScratchAllocationSource
namespace InitECandidate.Runtime
open Flapjack
/-- Every scratch allocation mask clears its low three bits, even on wraparound. -/
theorem scratchAllocationEnd_mask_aligned (pointer size : BitVec 64) :
    (scratchAllocationEnd pointer size).toNat % 8 = 0 := by
  have same : scratchAllocationEnd pointer size = allocationEnd (pointer-size-7) 0 := by
    simp [scratchAllocationEnd,allocationEnd,BitVec.sub_add_cancel]
  rw [same,allocationEnd_eq_align,panByteAlign_toNat64]
  omega
#print axioms scratchAllocationEnd_mask_aligned
end InitECandidate.Runtime
