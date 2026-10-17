import InitECandidate.Runtime.StateFreshTxSequence
namespace InitECandidate.Runtime
open Flapjack

/-- The eight literal constructors, including the first scoped declaration. -/
def stateFreshTxAllTables : List (Nat × Nat × Nat) :=
  (20,64,8) :: stateFreshTxRemainingTables

/-- Addresses and required key widths, in actual constructor execution order. -/
def stateFreshTxWidthRequirements (pointer : BitVec 64) : List (Nat × Nat × Nat) → List (BitVec 64 × BitVec 64)
  | [] => []
  | (width,capacity,_) :: rest =>
    (pointer,BitVec.ofNat 64 width) ::
      stateFreshTxWidthRequirements (stateFreshTxNextTable pointer width capacity) rest

/-- Width membership supplies all address-dependent premises; literal capacity,
width and state-field offset checks are discharged once for the frozen source. -/
theorem stateFreshTx_concrete_plan (widths : BitVec 64 → BitVec 64) (pointer : BitVec 64)
    (requirements : ∀ pair ∈ stateFreshTxWidthRequirements pointer stateFreshTxAllTables,
      widths pair.1 = pair.2) :
    StateFreshTxPlan widths pointer stateFreshTxAllTables := by
  simp only [stateFreshTxAllTables,stateFreshTxRemainingTables,stateFreshTxWidthRequirements,
    List.mem_cons,List.not_mem_nil,or_false] at requirements
  simp only [stateFreshTxAllTables,stateFreshTxRemainingTables,StateFreshTxPlan]
  refine ⟨requirements _ (Or.inl rfl),by decide,by decide,by decide,by decide,⟨6,rfl⟩,?_⟩
  refine ⟨requirements _ (Or.inr (Or.inl rfl)),by decide,by decide,by decide,by decide,⟨6,rfl⟩,?_⟩
  refine ⟨requirements _ (Or.inr (Or.inr (Or.inl rfl))),by decide,by decide,by decide,by decide,⟨6,rfl⟩,?_⟩
  refine ⟨requirements _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),by decide,by decide,by decide,by decide,⟨4,rfl⟩,?_⟩
  refine ⟨requirements _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),by decide,by decide,by decide,by decide,⟨4,rfl⟩,?_⟩
  refine ⟨requirements _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),by decide,by decide,by decide,by decide,⟨4,rfl⟩,?_⟩
  refine ⟨requirements _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),by decide,by decide,by decide,by decide,⟨4,rfl⟩,?_⟩
  exact ⟨requirements _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))),by decide,by decide,by decide,by decide,⟨4,rfl⟩,True.intro⟩

/-- Total safe allocation reservation and source clock for all eight tables. -/
theorem stateFreshTx_all_budgets :
    stateFreshTxAllocationBudget stateFreshTxAllTables = 22944 ∧
      stateFreshTxClockBudget stateFreshTxAllTables = 336 := by decide

/-- The cumulative reservation bounds the final frontier and prevents wraparound. -/
theorem stateFreshTx_frontier_bounds (specs : List (Nat × Nat × Nat)) :
    ∀ (widths : BitVec 64 → BitVec 64) (pointer : BitVec 64),
      StateFreshTxPlan widths pointer specs → pointer.toNat % 8 = 0 →
      pointer.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 →
      pointer.toNat ≤ (stateFreshTxFrontierAfter pointer specs).toNat ∧
      (stateFreshTxFrontierAfter pointer specs).toNat ≤ pointer.toNat + stateFreshTxAllocationBudget specs ∧
      (stateFreshTxFrontierAfter pointer specs).toNat % 8 = 0 := by
  induction specs with
  | nil =>
      intro widths pointer plan aligned budget
      exact ⟨Nat.le_refl _,Nat.le_refl _,aligned⟩
  | cons spec rest ih =>
      rcases spec with ⟨width,capacity,offset⟩
      intro widths pointer plan aligned budget
      obtain ⟨_,widthBound,capacityBound,_,_,_,tailPlan⟩ := plan
      have reserve : pointer.toNat + 81 * capacity + 114 + stateFreshTxAllocationBudget rest ≤ 33806089496 := by
        simpa only [stateFreshTxAllocationBudget,Nat.add_assoc] using budget
      obtain ⟨advances,upper,nextAligned⟩ := stateFreshTx_next_table_bounds pointer width capacity widthBound capacityBound (by omega)
      obtain ⟨lowerFinal,upperFinal,finalAligned⟩ := ih widths (stateFreshTxNextTable pointer width capacity) tailPlan nextAligned (by omega)
      change pointer.toNat ≤ (stateFreshTxFrontierAfter (stateFreshTxNextTable pointer width capacity) rest).toNat ∧ _
      exact ⟨by omega,by change (stateFreshTxFrontierAfter (stateFreshTxNextTable pointer width capacity) rest).toNat ≤ pointer.toNat + (81 * capacity + 114 + stateFreshTxAllocationBudget rest); omega,finalAligned⟩

/-- Concrete reservation for all eight actual transaction-table constructors. -/
theorem stateFreshTx_all_frontier_bounds (widths : BitVec 64 → BitVec 64) (pointer : BitVec 64)
    (requirements : ∀ pair ∈ stateFreshTxWidthRequirements pointer stateFreshTxAllTables, widths pair.1 = pair.2)
    (aligned : pointer.toNat % 8 = 0) (budget : pointer.toNat + 22944 ≤ 33806089496) :
    pointer.toNat ≤ (stateFreshTxFrontierAfter pointer stateFreshTxAllTables).toNat ∧
      (stateFreshTxFrontierAfter pointer stateFreshTxAllTables).toNat ≤ pointer.toNat + 22944 ∧
      (stateFreshTxFrontierAfter pointer stateFreshTxAllTables).toNat % 8 = 0 := by
  simpa only [stateFreshTx_all_budgets.1] using
    stateFreshTx_frontier_bounds stateFreshTxAllTables widths pointer (stateFreshTx_concrete_plan widths pointer requirements) aligned
      (by simpa only [stateFreshTx_all_budgets.1] using budget)

#print axioms stateFreshTx_concrete_plan
#print axioms stateFreshTx_frontier_bounds
#print axioms stateFreshTx_all_frontier_bounds
#print axioms stateFreshTx_all_budgets
end InitECandidate.Runtime
