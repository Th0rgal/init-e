import InitECandidate.Runtime.StateFreshTxWidthExtension
namespace InitECandidate.Runtime
open Flapjack

/-- Every width literal belongs to the supported journal-key family. -/
def StateFreshTxSupportedWidths (specs : List (Nat × Nat × Nat)) : Prop :=
  ∀ width capacity offset, (width,capacity,offset) ∈ specs → width = 20 ∨ width = 32 ∨ width = 52

/-- A constructor address plan assigns a supported width to every inserted
registered table and retains the supported widths of earlier tables. -/
theorem stateFreshTx_registry_supported_widths (specs : List (Nat × Nat × Nat)) :
    ∀ (widths : BitVec 64 → BitVec 64) (pointer : BitVec 64) (tables : Set (BitVec 64)),
      StateFreshTxPlan widths pointer specs → StateFreshTxSupportedWidths specs →
      (∀ table ∈ tables, widths table = 20 ∨ widths table = 32 ∨ widths table = 52) →
      ∀ table ∈ stateFreshTxRegistryAfter pointer specs tables,
        widths table = 20 ∨ widths table = 32 ∨ widths table = 52 := by
  induction specs with
  | nil => intro widths pointer tables plan literals old; exact old
  | cons spec rest ih =>
      rcases spec with ⟨width,capacity,offset⟩
      intro widths pointer tables plan literals old
      have atPointer := plan.1
      have tail := plan.2.2.2.2.2.2
      have supported := literals width capacity offset (List.mem_cons_self ..)
      apply ih widths (stateFreshTxNextTable pointer width capacity) (insert pointer tables) tail
        (by intro w c o member; exact literals w c o (List.mem_cons_of_mem _ member))
      intro table member
      rcases Set.mem_insert_iff.mp member with same | previous
      · subst table
        rw [atPointer]
        rcases supported with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exact old table previous

theorem stateFreshTx_all_supported_widths : StateFreshTxSupportedWidths stateFreshTxAllTables := by
  intro width capacity offset member
  simp [stateFreshTxAllTables,stateFreshTxRemainingTables] at member
  rcases member with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> simp

#print axioms stateFreshTx_registry_supported_widths
#print axioms stateFreshTx_all_supported_widths
end InitECandidate.Runtime
