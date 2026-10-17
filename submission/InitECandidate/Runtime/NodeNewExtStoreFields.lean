import InitECandidate.Runtime.NodeNewExtStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The original constructor's exact memory post-state records the extension
kind, path pointer/length and child at their authoritative offsets. -/
theorem nodeNewExtStoresPost_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib size child : BitVec 64) :
    (nodeNewExtStoresPost state pointer nib size child).memory pointer = .word 2 ∧
    (nodeNewExtStoresPost state pointer nib size child).memory (pointer + 32) = .word nib ∧
    (nodeNewExtStoresPost state pointer nib size child).memory (pointer + 40) = .word size ∧
    (nodeNewExtStoresPost state pointer nib size child).memory (pointer + 48) = .word child := by
  simp [nodeNewExtStoresPost,sourceWriteWord,emptyLocalsHOLFinite]

/-- Stores into the fresh56-byte record preserve all earlier memory. -/
theorem nodeNewExtStoresPost_before {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib size child : BitVec 64) (bounded : pointer.toNat + 56 ≤ 33806089496)
    (address : BitVec 64) (before : address.toNat < pointer.toNat) :
    (nodeNewExtStoresPost state pointer nib size child).memory address = state.memory address := by
  have outside : ∀ offset : Nat, offset < 56 → address ≠ pointer + BitVec.ofNat 64 offset := by
    intro offset inside equal
    have literal : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have nextNat : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [literal]; change pointer.toNat + offset < 2^64; omega),literal]
    have same := congrArg BitVec.toNat equal
    rw [nextNat] at same
    omega
  have notPointer : address ≠ pointer := by intro equal; subst address; omega
  simp [nodeNewExtStoresPost,sourceWriteWord,emptyLocalsHOLFinite,notPointer,
    outside 8 (by decide),outside 16 (by decide),outside 24 (by decide),
    outside 32 (by decide),outside 40 (by decide),outside 48 (by decide)]

#print axioms nodeNewExtStoresPost_fields
#print axioms nodeNewExtStoresPost_before
end InitECandidate.Runtime
