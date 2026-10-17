import InitECandidate.Runtime.StateFreshTxConcretePlan
namespace InitECandidate.Runtime
open Flapjack

/-- A plan depends only on width bindings at or above its initial frontier. -/
theorem StateFreshTxPlan.congr_above (specs : List (Nat × Nat × Nat)) :
    ∀ (before after : BitVec 64 → BitVec 64) (pointer : BitVec 64),
      StateFreshTxPlan before pointer specs →
      pointer.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 →
      (∀ address, pointer.toNat ≤ address.toNat → after address = before address) →
      StateFreshTxPlan after pointer specs := by
  induction specs with
  | nil => intro before after pointer plan budget agree; trivial
  | cons spec rest ih =>
      rcases spec with ⟨width,capacity,offset⟩
      intro before after pointer plan budget agree
      obtain ⟨atPointer,widthBound,capacityBound,large,offsetBound,power,tail⟩ := plan
      have reserve : pointer.toNat + 81 * capacity + 114 + stateFreshTxAllocationBudget rest ≤ 33806089496 := by
        simpa only [stateFreshTxAllocationBudget,Nat.add_assoc] using budget
      obtain ⟨advance,upper,_⟩ := stateFreshTx_next_table_bounds pointer width capacity widthBound capacityBound (by omega)
      refine ⟨(agree pointer (Nat.le_refl _)).trans atPointer,widthBound,capacityBound,large,offsetBound,power,?_⟩
      exact ih before after _ tail (by omega) (by intro address lower; exact agree address (by omega))

/-- Literal requirements independent of any address-indexed width map. -/
def StateFreshTxLiterals : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (width,capacity,offset) :: rest =>
    width ≤ 52 ∧ capacity < 2 ^ 64 ∧ 1 < capacity ∧ offset < 72 ∧
      (∃ bits, capacity = 2 ^ bits) ∧ StateFreshTxLiterals rest

/-- Fresh constructors admit a compatible width map while preserving every
binding below their initial frontier. Strict frontier growth excludes collisions. -/
theorem stateFreshTx_width_extension (specs : List (Nat × Nat × Nat)) :
    ∀ (base : BitVec 64 → BitVec 64) (pointer : BitVec 64),
      StateFreshTxLiterals specs →
      pointer.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 →
      ∃ widths, StateFreshTxPlan widths pointer specs ∧
        ∀ address, address.toNat < pointer.toNat → widths address = base address := by
  induction specs with
  | nil => intro base pointer literals budget; exact ⟨base,True.intro,by intros; rfl⟩
  | cons spec rest ih =>
      rcases spec with ⟨width,capacity,offset⟩
      intro base pointer literals budget
      obtain ⟨widthBound,capacityBound,large,offsetBound,power,tailLiterals⟩ := literals
      have reserve : pointer.toNat + 81 * capacity + 114 + stateFreshTxAllocationBudget rest ≤ 33806089496 := by
        simpa only [stateFreshTxAllocationBudget,Nat.add_assoc] using budget
      obtain ⟨advance,upper,_⟩ := stateFreshTx_next_table_bounds pointer width capacity widthBound capacityBound (by omega)
      obtain ⟨tailWidths,tailPlan,preserve⟩ := ih base (stateFreshTxNextTable pointer width capacity) tailLiterals (by omega)
      let widths := fun address => if address = pointer then BitVec.ofNat 64 width else tailWidths address
      have tailUpdated : StateFreshTxPlan widths (stateFreshTxNextTable pointer width capacity) rest :=
        StateFreshTxPlan.congr_above rest tailWidths widths _ tailPlan (by omega) (by
          intro address lower
          have different : address ≠ pointer := by intro same; subst address; omega
          simp [widths,different])
      refine ⟨widths,⟨by simp [widths],widthBound,capacityBound,large,offsetBound,power,tailUpdated⟩,?_⟩
      intro address lower
      have different : address ≠ pointer := by intro same; subst address; omega
      simp only [widths,if_neg different]
      exact preserve address (by omega)

/-- The concrete eight constructors can always extend the earlier width map
when their checked allocation reservation fits. -/
theorem stateFreshTx_all_width_extension (base : BitVec 64 → BitVec 64) (pointer : BitVec 64)
    (budget : pointer.toNat + 22944 ≤ 33806089496) :
    ∃ widths, StateFreshTxPlan widths pointer stateFreshTxAllTables ∧
      ∀ address, address.toNat < pointer.toNat → widths address = base address := by
  apply stateFreshTx_width_extension stateFreshTxAllTables base pointer
  · simp only [stateFreshTxAllTables,stateFreshTxRemainingTables,StateFreshTxLiterals]
    simp only [show (∃ bits : Nat, 64 = 2 ^ bits) from ⟨6,rfl⟩,
      show (∃ bits : Nat, 16 = 2 ^ bits) from ⟨4,rfl⟩]
    decide
  · simpa only [stateFreshTx_all_budgets.1] using budget

#print axioms StateFreshTxPlan.congr_above
#print axioms stateFreshTx_width_extension
#print axioms stateFreshTx_all_width_extension
end InitECandidate.Runtime
