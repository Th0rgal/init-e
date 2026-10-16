import InitECandidate.Runtime.AllocationSeparation
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Mathlib.Tactic.IntervalCases
namespace InitECandidate.Runtime
open Flapjack

def allocationEnd (pointer size : BitVec 64) : BitVec 64 :=
  (pointer + size + 7) &&& (0 - 8)

/-- The source allocation mask clears the low three bits of its rounded sum. -/
theorem allocationEnd_eq_align (pointer size : BitVec 64) :
    allocationEnd pointer size = panByteAlignHOL (pointer + size + 7) := by
  unfold allocationEnd
  rw [← riscvByteAlignHOL_eq_panByteAlignHOL]
  change (pointer + size + 7) &&& (0 - 8) = ((pointer + size + 7) >>> 3) <<< 3
  apply BitVec.eq_of_getLsbD_eq
  intro bit bounded
  interval_cases bit <;> simp [BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight]

/-- The allocator's first unsigned guard is a natural sum bound when the
current pointer is inside the heap. -/
theorem allocationGuard_sum_bound (pointer size : BitVec 64)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (guard : size ≤ (33806089496 : BitVec 64) - pointer) :
    pointer.toNat + size.toNat ≤ 33806089496 := by
  have pointerLe : pointer ≤ (33806089496 : BitVec 64) := BitVec.le_def.mpr pointerBound
  have gap : ((33806089496 : BitVec 64) - pointer).toNat = 33806089496 - pointer.toNat := by
    rw [BitVec.toNat_sub_of_le pointerLe]
    rfl
  have sizeBound := BitVec.le_def.mp guard
  rw [gap] at sizeBound
  omega

/-- Exact rounded allocation endpoint, without word overflow. -/
theorem allocationEnd_toNat (pointer size : BitVec 64)
    (bounded : pointer.toNat + size.toNat ≤ 33806089496) :
    (allocationEnd pointer size).toNat = (pointer.toNat + size.toNat + 7) / 8 * 8 := by
  have sumBound : pointer.toNat + size.toNat < 2 ^ 64 := by omega
  have added := BitVec.toNat_add_of_lt sumBound
  have paddedBound : (pointer + size).toNat + (7 : BitVec 64).toNat < 2 ^ 64 := by
    rw [added]
    change pointer.toNat + size.toNat + 7 < 2 ^ 64
    omega
  rw [allocationEnd_eq_align,panByteAlign_toNat64,BitVec.toNat_add_of_lt paddedBound,added]
  rfl

/-- Successful allocation endpoints cover every requested byte, have less
than eight bytes padding, and remain eight-byte aligned. -/
theorem allocationEnd_covers (pointer size : BitVec 64)
    (bounded : pointer.toNat + size.toNat ≤ 33806089496) :
    pointer.toNat + size.toNat ≤ (allocationEnd pointer size).toNat ∧
      (allocationEnd pointer size).toNat < pointer.toNat + size.toNat + 8 ∧
      (allocationEnd pointer size).toNat % 8 = 0 := by
  rw [allocationEnd_toNat pointer size bounded]
  have division := Nat.mod_add_div (pointer.toNat + size.toNat + 7) 8
  have remainder := Nat.mod_lt (pointer.toNat + size.toNat + 7) (by decide : 0 < 8)
  exact ⟨by omega,by omega,by omega⟩

#print axioms allocationEnd_eq_align
#print axioms allocationGuard_sum_bound
#print axioms allocationEnd_toNat
#print axioms allocationEnd_covers
end InitECandidate.Runtime
