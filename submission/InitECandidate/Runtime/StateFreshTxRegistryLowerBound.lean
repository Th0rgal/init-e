import InitECandidate.Runtime.StateFreshTxWidthExtension
namespace InitECandidate.Runtime
open Flapjack

/-- Every new table header lies beyond any lower bound of the initial frontier;
existing registered headers retain the same bound. -/
theorem stateFreshTx_registry_lower_bound (specs : List (Nat × Nat × Nat)) :
    ∀ (pointer : BitVec 64) (tables : Set (BitVec 64)) (lower : Nat),
      StateFreshTxLiterals specs → lower ≤ pointer.toNat →
      (∀ table ∈ tables, lower ≤ table.toNat) →
      pointer.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 →
      ∀ table ∈ stateFreshTxRegistryAfter pointer specs tables, lower ≤ table.toNat := by
  induction specs with
  | nil => intro pointer tables lower literals before headers budget; exact headers
  | cons spec rest ih =>
      rcases spec with ⟨width,capacity,offset⟩
      intro pointer tables lower literals before headers budget
      obtain ⟨widthBound,capacityBound,_,_,_,tail⟩ := literals
      have reserve : pointer.toNat + 81 * capacity + 114 + stateFreshTxAllocationBudget rest ≤ 33806089496 := by
        simpa only [stateFreshTxAllocationBudget,Nat.add_assoc] using budget
      obtain ⟨advance,upper,_⟩ := stateFreshTx_next_table_bounds pointer width capacity widthBound capacityBound (by omega)
      apply ih (stateFreshTxNextTable pointer width capacity) (insert pointer tables) lower tail (by omega) ?_ (by omega)
      intro table member
      rcases Set.mem_insert_iff.mp member with same | old
      · simpa only [same] using before
      · exact headers table old

theorem stateFreshTx_all_literals : StateFreshTxLiterals stateFreshTxAllTables := by
  simp only [stateFreshTxAllTables,stateFreshTxRemainingTables,StateFreshTxLiterals]
  simp only [show (∃ bits : Nat, 64 = 2 ^ bits) from ⟨6,rfl⟩,
    show (∃ bits : Nat, 16 = 2 ^ bits) from ⟨4,rfl⟩]
  decide

#print axioms stateFreshTx_registry_lower_bound
#print axioms stateFreshTx_all_literals
end InitECandidate.Runtime
