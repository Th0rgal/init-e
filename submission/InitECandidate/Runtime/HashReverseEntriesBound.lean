import InitECandidate.Runtime.HashOrderEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Occupied slots carry readable reverse positions within the live order
prefix. Empty slots impose no condition on uninitialized reverse-array cells. -/
def HashReverseEntriesBound {F : Type} (used orderPos capacity items : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
    hashOccupancyRead state used slot ≠ some 0 →
    ∃ position : BitVec 64, state.memory (orderPos + slot * 8) = .word position ∧
      position.toNat < items.toNat

/-- Constructor zeroing establishes the reverse invariant without reading
any uninitialized reverse entry. -/
theorem HashReverseEntriesBound.empty {F : Type}
    (state : PanSemStateFiniteExact 64 F) (used orderPos capacity : BitVec 64)
    (zeroed : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot = some 0) :
    HashReverseEntriesBound used orderPos capacity 0 state := by
  intro slot inside occupied
  exact False.elim (occupied (zeroed slot inside))

/-- A memory frame on occupancy and reverse entries transfers the bound,
even when the body changes unrelated memory and locals. -/
theorem HashReverseEntriesBound.framed {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used orderPos capacity items : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (reverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8)) :
    HashReverseEntriesBound used orderPos capacity items post := by
  intro slot inside occupied
  obtain ⟨position,cell,bound⟩ := entries slot inside (by rw [← occupancy slot inside]; exact occupied)
  exact ⟨position,(reverse slot inside).trans cell,bound⟩

theorem HashReverseEntriesBound.after_read {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used orderPos capacity items : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (memory : post.memory = state.memory) (domain : post.memaddrs = state.memaddrs)
    (endian : post.be = state.be) : HashReverseEntriesBound used orderPos capacity items post := by
  apply entries.framed state post used orderPos capacity items
  · intro slot inside
    unfold hashOccupancyRead
    rw [memory,domain,endian]
  · intro slot inside
    rw [memory]

#print axioms HashReverseEntriesBound.empty
#print axioms HashReverseEntriesBound.framed
#print axioms HashReverseEntriesBound.after_read
end InitECandidate.Runtime
