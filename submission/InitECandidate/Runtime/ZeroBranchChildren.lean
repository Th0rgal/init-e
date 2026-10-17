import InitECandidate.Runtime.ZeroBytesWord
import InitECandidate.Runtime.BranchChildrenIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The original 176-byte branch zeroing establishes all sixteen null child
slots, independent of the old memory and the choice of live-node registry. -/
theorem zeroBranch_child_slots {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (zero : ZeroBytePrefix state pointer 176)
    (aligned : pointer.toNat % 8 = 0) (bounded : pointer.toNat + 176 < 2^64) :
    ∀ slot : Nat, slot < 16 → state.memory (branchChildAddress pointer slot) = .word 0 := by
  intro slot small
  have offsetBound : 32 + slot * 8 + 8 ≤ 176 := by omega
  have offsetAligned : (pointer.toNat + (32 + slot * 8)) % 8 = 0 := by omega
  have word := zero.word state pointer 176 (32 + slot * 8) offsetBound bounded offsetAligned
  have address : branchChildAddress pointer slot = pointer + BitVec.ofNat 64 (32 + slot * 8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
  rw [address]
  exact word

theorem zeroBranch_children_registry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live : Set (BitVec 64)) (pointer : BitVec 64) (zero : ZeroBytePrefix state pointer 176)
    (aligned : pointer.toNat % 8 = 0) (bounded : pointer.toNat + 176 < 2^64) :
    BranchChildrenIn live {pointer} state := by
  intro node member slot small child loaded
  have same : node = pointer := Set.mem_singleton_iff.mp member
  subst node
  have zeroSlot := zeroBranch_child_slots state pointer zero aligned bounded slot small
  have childZero : child = 0 := HolWordLab.word.inj (loaded.symm.trans zeroSlot)
  exact Or.inl childZero

#print axioms zeroBranch_child_slots
#print axioms zeroBranch_children_registry
end InitECandidate.Runtime
