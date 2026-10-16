import InitECandidate.Runtime.HashTableReadInvariant32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Updating an in-range value preserves headers, domains and count agreement. -/
theorem HashTableInvariant32.write_value {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity count index value : BitVec 64) (bits : Nat)
    (invariant : HashTableInvariant32 table capacity count bits state)
    (inside : index.toNat < capacity.toNat) :
    HashTableInvariant32 table capacity count bits
      (sourceWriteWord state (htabNewValues table 32 capacity + index * 8) value) := by
  obtain ⟨va,ua,oa,ra,hv,vu,uo,orr,limit⟩ := htabNew_insertion_layout table 32 capacity (by decide) invariant.heapBudget
  have valueAddress := hashFind_slot_address (htabNewValues table 32 capacity) index 8 capacity inside
    (by change (htabNewValues table 32 capacity).toNat + capacity.toNat * 8 ≤ 33806089496; omega) va (by decide)
  have headerSeparate : ∀ offset : Nat, offset ≤ 64 →
      table + BitVec.ofNat 64 offset ≠ htabNewValues table 32 capacity + index * 8 := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    intro same
    have equal := congrArg BitVec.toNat same
    rw [address,valueAddress.1] at equal
    omega
  have separate := hashSet_value_separate (htabNewValues table 32 capacity) (htabNewUsed table 32 capacity) capacity index
    inside va ua vu (by omega)
  have preserved := sourceWriteWord_occupancy_preserved state capacity (htabNewUsed table 32 capacity)
    (htabNewValues table 32 capacity + index * 8) value separate
  refine {
    code := invariant.code
    power := invariant.power
    heapBudget := invariant.heapBudget
    domain := invariant.domain
    agreement := by rw [preserved]; exact invariant.agreement
    room := invariant.room
    cell0 := by
      change (sourceWriteWord state _ value).memory (table + 0) = _
      simp only [sourceWriteWord]
      have different : table + (0 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 0 (by decide)
      rw [if_neg different]
      exact invariant.cell0
    cell8 := by
      change (sourceWriteWord state _ value).memory (table + 8) = _
      simp only [sourceWriteWord]
      have different : table + (8 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 8 (by decide)
      rw [if_neg different]
      exact invariant.cell8
    cell16 := by
      change (sourceWriteWord state _ value).memory (table + 16) = _
      simp only [sourceWriteWord]
      have different : table + (16 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 16 (by decide)
      rw [if_neg different]
      exact invariant.cell16
    cell24 := by
      change (sourceWriteWord state _ value).memory (table + 24) = _
      simp only [sourceWriteWord]
      have different : table + (24 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 24 (by decide)
      rw [if_neg different]
      exact invariant.cell24
    cell32 := by
      change (sourceWriteWord state _ value).memory (table + 32) = _
      simp only [sourceWriteWord]
      have different : table + (32 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 32 (by decide)
      rw [if_neg different]
      exact invariant.cell32
    cell40 := by
      change (sourceWriteWord state _ value).memory (table + 40) = _
      simp only [sourceWriteWord]
      have different : table + (40 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 40 (by decide)
      rw [if_neg different]
      exact invariant.cell40
    cell48 := by
      change (sourceWriteWord state _ value).memory (table + 48) = _
      simp only [sourceWriteWord]
      have different : table + (48 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 48 (by decide)
      rw [if_neg different]
      exact invariant.cell48
    cell56 := by
      change (sourceWriteWord state _ value).memory (table + 56) = _
      simp only [sourceWriteWord]
      have different : table + (56 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 56 (by decide)
      rw [if_neg different]
      exact invariant.cell56
    cell64 := by
      change (sourceWriteWord state _ value).memory (table + 64) = _
      simp only [sourceWriteWord]
      have different : table + (64 : BitVec 64) ≠ htabNewValues table 32 capacity + index * 8 := headerSeparate 64 (by decide)
      rw [if_neg different]
      exact invariant.cell64
  }

#print axioms HashTableInvariant32.write_value
end InitECandidate.Runtime
