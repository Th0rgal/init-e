import InitECandidate.Runtime.HashEmptyEntryInvariants
import InitECandidate.Runtime.HashTableReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every occupied value in this table points into the target registry.
The array pointers and capacity are read from the actual table header. -/
def HashTableValuesIn {F : Type} (table : BitVec 64) (targets : Set (BitVec 64))
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ capacity used values : BitVec 64,
    state.memory (table + 16) = .word capacity →
    state.memory (table + 48) = .word used → state.memory (table + 40) = .word values →
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot ≠ some 0 →
      ∀ value : BitVec 64, state.memory (values + slot * 8) = .word value → value ∈ targets

/-- Read-only execution retains occupancy observations, including inaccessible cells. -/
theorem hashOccupancyRead_after_read {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (used : BitVec 64) (memory : post.memory = state.memory)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    hashOccupancyRead post used = hashOccupancyRead state used := by
  funext slot
  unfold hashOccupancyRead panMemLoadByteHOL
  simp only [memory,endian]
  by_cases available : post.memaddrs (panByteAlignHOL (used + slot))
  · have before : state.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
    simp only [if_pos available,if_pos before]
  · have before : ¬state.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
    simp only [if_neg available,if_neg before]

/-- Enlarging the registry retains all existing pointer memberships. -/
theorem HashTableValuesIn.mono {F : Type} {state : PanSemStateFiniteExact 64 F}
    {table : BitVec 64} {targets nextTargets : Set (BitVec 64)}
    (entries : HashTableValuesIn table targets state) (subset : targets ⊆ nextTargets) :
    HashTableValuesIn table nextTargets state := by
  intro capacity used values capField usedField valuesField slot inside occupied value cell
  exact subset (entries capacity used values capField usedField valuesField slot inside occupied value cell)

/-- The pointer-membership predicate is independent of locals, clock, globals,
and code, and is retained by read-only execution. -/
theorem HashTableValuesIn.after_read {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {table : BitVec 64} {targets : Set (BitVec 64)}
    (entries : HashTableValuesIn table targets state) (memory : post.memory = state.memory)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableValuesIn table targets post := by
  intro capacity used values capField usedField valuesField slot inside occupied value cell
  apply entries capacity used values (by rw [← memory]; exact capField)
    (by rw [← memory]; exact usedField) (by rw [← memory]; exact valuesField) slot inside
    (by rw [← hashOccupancyRead_after_read state post used memory domain endian]; exact occupied) value
  rw [← memory]; exact cell

/-- A newly empty table satisfies pointer membership for any target registry;
uninitialized value cells are never treated as live pointers. -/
theorem HashTableValuesIn.empty {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity used : BitVec 64) (targets : Set (BitVec 64))
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used)
    (empty : hashOccupiedCount capacity (hashOccupancyRead state used) = 0) :
    HashTableValuesIn table targets state := by
  intro otherCapacity otherUsed otherValues capCell usedCell valuesCell slot inside occupied value cell
  have capEq : otherCapacity = capacity := by
    simpa only [HolWordLab.word.injEq] using capCell.symm.trans capField
  have usedEq : otherUsed = used := by
    simpa only [HolWordLab.word.injEq] using usedCell.symm.trans usedField
  subst otherCapacity
  subst otherUsed
  exact False.elim (occupied (hashOccupiedCount_zero_reads capacity (hashOccupancyRead state used) empty slot inside))

/-- The complete empty-table invariant initializes pointer membership. -/
theorem HashTableReady.values_in_empty {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos pointer : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos 0 bits pointer state)
    (targets : Set (BitVec 64)) : HashTableValuesIn table targets state := by
  apply HashTableValuesIn.empty state table capacity used targets ready.live.arrays.cell16 ready.live.arrays.cell48
  simpa using ready.live.arrays.agreement.symm

#print axioms HashTableReady.values_in_empty
#print axioms hashOccupancyRead_after_read
#print axioms HashTableValuesIn.mono
#print axioms HashTableValuesIn.after_read
#print axioms HashTableValuesIn.empty
end InitECandidate.Runtime
