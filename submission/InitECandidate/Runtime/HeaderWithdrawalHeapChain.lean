import InitECandidate.Runtime.HeaderWithdrawalEntryGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The heap chain step is pure arithmetic: an 8-aligned frontier that does not wrap advances by the
64-byte request, with **no** allocator-room (`HEAP_END`) cap. A run that gets here therefore never
needs to assume that all `nwd` allocations fit. -/
theorem wd_heap_step_no_cap (pointer : BitVec 64)
    (aligned : pointer.toNat % 8 = 0) (nowrap : pointer.toNat + 71 < 2^64) :
    allocationEnd pointer 64 = pointer + 64#64 := by
  have s64 : BitVec.toNat (64 : BitVec 64) = 64 := by decide
  have s64' : (64#64 : BitVec 64).toNat = 64 := by decide
  have s7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
  have ptrFit : pointer.toNat + 64 < 2^64 := by omega
  have sumVal : BitVec.toNat (pointer + 64 + 7) = pointer.toNat + 71 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, s64, s7]
    omega
  have rightVal : (pointer + 64#64 : BitVec 64).toNat = pointer.toNat + 64 := by
    rw [BitVec.toNat_add, s64']
    omega
  apply BitVec.eq_of_toNat_eq
  rw [allocationEnd_eq_align, panByteAlign_toNat64, sumVal, rightVal]
  omega

/-- A successful allocation request (`size ≤ HEAP_END - pointer`) together with the allocator's
frontier invariant (`pointer ≤ HEAP_END`) gives the per-iteration no-wrap fact. The frontier bound is
explicit: it is not inferred from the subtraction alone, which would wrap above `HEAP_END`. -/
theorem wd_alloc_success_nowrap (pointer size : BitVec 64)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (sizeVal : size.toNat = 64) :
    pointer.toNat + 71 < 2^64 := by
  have capVal : (33806089496 : BitVec 64).toNat = 33806089496 := by decide
  have pLe : pointer ≤ (33806089496 : BitVec 64) := BitVec.le_def.mpr pointerBound
  have sum := BitVec.le_def.mp request
  rw [BitVec.toNat_sub_of_le pLe, capVal] at sum
  omega

#print axioms wd_heap_step_no_cap
#print axioms wd_alloc_success_nowrap
end InitECandidate.Runtime
