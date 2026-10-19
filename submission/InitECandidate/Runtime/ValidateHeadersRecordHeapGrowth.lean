import InitECandidate.Runtime.AllocationRound
import InitECandidate.Runtime.ValidateHeadersParentReaches
/-!
The heap growth of one actual validation iteration.

An iteration allocates twice: the header decoder allocates the RLP pointer buffer (`count*16`
bytes, fewer than 21 pointers per header) and then the whole 248-byte header record.  Both
allocations are `allocationEnd`s, so each has fewer than eight bytes of padding, and the record
sits strictly after the pointer buffer.  Together this bounds the iteration's heap growth by
`headerCarryRoom` (624 bytes), which is exactly why that constant is the room the decode call
requires: `21*16 + 8` of pointer buffer, `248 + 8` of record, well under 624.

The bound is derived from the actual allocation geometry, not assumed: `record` is the
`allocationEnd` of the pointer buffer and `nextHeap` is the `allocationEnd` of the record.
-/
namespace InitECandidate.Runtime
open Flapjack
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- One iteration's allocations grow the heap by at most `headerCarryRoom` bytes, given the
inner pointer count (`21*16`) and the record's own room. -/
theorem validate_headers_record_heap_growth (heapStart dcount record nextHeap : BitVec 64)
    (recordEq : record = allocationEnd heapStart (dcount * 16))
    (nextEq : nextHeap = allocationEnd record 248)
    (countBound : (dcount * 16).toNat ≤ 21 * 16)
    (heapBound : heapStart.toNat ≤ 33806089496)
    (recordRoom : record.toNat + 248 ≤ 33806089496)
    (recordAbove : heapStart.toNat + 21 * 16 ≤ record.toNat) :
    nextHeap.toNat ≤ heapStart.toNat + headerCarryRoom := by
  have bufferSum : heapStart.toNat + (dcount * 16).toNat ≤ 33806089496 := by
    have := countBound
    omega
  have bufferTrace := allocationEnd_covers heapStart (dcount * 16) bufferSum
  have recordExact : record.toNat = (allocationEnd heapStart (dcount * 16)).toNat := by
    rw [recordEq]
  have recordSum : record.toNat + (248 : BitVec 64).toNat ≤ 33806089496 := by
    have same : (248 : BitVec 64).toNat = 248 := rfl
    rw [same]
    exact recordRoom
  have nextTrace := allocationEnd_covers record 248 recordSum
  have nextExact : nextHeap.toNat = (allocationEnd record 248).toNat := by
    rw [nextEq]
  have room : (248 : BitVec 64).toNat = 248 := rfl
  have bufferGap : (allocationEnd heapStart (dcount * 16)).toNat < heapStart.toNat + 21 * 16 + 8 := by
    have := bufferTrace.2.1
    omega
  have nextGap := nextTrace.2.1
  rw [room] at nextGap
  unfold headerCarryRoom
  omega

#print axioms validate_headers_record_heap_growth
end InitECandidate.Runtime
