import InitECandidate.Runtime.ValidateHeadersRankRoom
import InitECandidate.Runtime.Bn254AccelInitSource
/-!
The source-connected heap growth of one validation iteration: `nextHeap < heapStart + 624`.

The decode call's checked contract reports a count that is 21 or 23 - so `count.toNat <= 23`, an
upper bound, not the 21 of the lower frontier.  With `heapCapped : heapStart + 624 <= cap` the
buffer request is then inside the cap (`23*16 = 368`, plus the record's `248`, inside 624), so
`allocationEnd_covers` applies and gives `record < heapStart + 368 + 8`.  The record allocation
itself is exact rather than padded: the record endpoint is eight-byte aligned and 248 is a
multiple of eight, so `allocationEnd_aligned_exact` turns the second allocation into
`nextHeap = record + 248`.  Hence `nextHeap < heapStart + 624`.
-/
namespace InitECandidate.Runtime
open Flapjack
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- **Growth of one actual iteration.** With the contract's `count.toNat ≤ 23`, the caller's
624-byte heap room and the endpoint's own allocation equations, the heap after the iteration is
strictly below `heapStart + 624`. -/
theorem validate_headers_actual_iteration_growth (heapStart count record nextHeap : BitVec 64)
    (heapCapped : heapStart.toNat + headerCarryRoom ≤ 33806089496)
    (countBound : count.toNat ≤ 23)
    (recordEq : record = allocationEnd heapStart (count * 16))
    (nextEq : nextHeap = allocationEnd record 248)
    (recordAligned : record.toNat % 8 = 0)
    (recordRoom : record.toNat + 248 ≤ 33806089496) :
    nextHeap.toNat < heapStart.toNat + headerCarryRoom := by
  have sizeBound : count.toNat * 16 ≤ 368 := by omega
  have sizeNat : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have bufferSum : heapStart.toNat + (count * 16).toNat ≤ 33806089496 := by
    rw [sizeNat]
    unfold headerCarryRoom at heapCapped
    omega
  have covered := allocationEnd_covers heapStart (count * 16) bufferSum
  have recordBelow : record.toNat < heapStart.toNat + 368 + 8 := by
    have raw := covered.2.1
    rw [sizeNat] at raw
    rw [recordEq]
    omega
  have sizeAligned : (248 : BitVec 64).toNat % 8 = 0 := rfl
  have exactEnd := allocationEnd_aligned_exact record 248 recordAligned sizeAligned recordRoom
  unfold headerCarryRoom
  rw [nextEq, exactEnd]
  have boundNat : record.toNat + (248 : BitVec 64).toNat < 2^64 := by
    have same : (248 : BitVec 64).toNat = 248 := rfl
    rw [same]
    omega
  have added := BitVec.toNat_add_of_lt boundNat
  have sizeOf : (248 : BitVec 64).toNat = 248 := rfl
  rw [added, sizeOf]
  omega

#print axioms validate_headers_actual_iteration_growth
end InitECandidate.Runtime
