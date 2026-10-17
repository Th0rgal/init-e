import InitECandidate.Runtime.ScratchAllocationGeometry
namespace InitECandidate.Runtime
open Flapjack

/-- Any field within a descending scratch allocation lies below the original
frontier, and adding its offset does not wrap a machine word. -/
theorem scratchAllocation_field_nat (scratch size : BitVec 64) (field : Nat)
    (fits : size.toNat ≤ scratch.toNat) (inside : field < size.toNat) :
    (scratchAllocationEnd scratch size + BitVec.ofNat 64 field).toNat =
      (scratchAllocationEnd scratch size).toNat + field ∧
    (scratchAllocationEnd scratch size + BitVec.ofNat 64 field).toNat < scratch.toNat := by
  have before := scratchAllocationEnd_before scratch size fits
  have sizeBound := size.isLt
  have top := scratch.isLt
  have small : field < 2^64 := by omega
  have noWrap : (scratchAllocationEnd scratch size).toNat + (BitVec.ofNat 64 field).toNat < 2^64 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    omega
  rw [BitVec.toNat_add_of_lt noWrap,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  exact ⟨rfl,by omega⟩

#print axioms scratchAllocation_field_nat
end InitECandidate.Runtime
