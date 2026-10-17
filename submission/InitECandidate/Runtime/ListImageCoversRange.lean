import Init.Data.List.Perm
import Init.Data.List.Erase
import Init.Data.List.Nat.Range
namespace InitECandidate.Runtime

/-- Injectivity restricted to list members suffices to preserve distinctness. -/
theorem list_nodup_map_of_injective_on {A B : Type} (items : List A) (map : A → B)
    (distinct : items.Nodup)
    (injective : ∀ x ∈ items, ∀ y ∈ items, map x = map y → x = y) :
    (items.map map).Nodup := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    have parts := List.nodup_cons.mp distinct
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih parts.2 ?_⟩
    · intro member
      obtain ⟨item,inTail,equal⟩ := List.mem_map.mp member
      have same := injective head (by simp) item (by simp [inTail]) equal.symm
      exact parts.1 (same ▸ inTail)
    · intro x hx y hy equal
      exact injective x (by simp [hx]) y (by simp [hy]) equal

/-- A distinct bounded image with exactly as many elements as the range
covers every index. This is a finite pigeonhole argument using lists only. -/
theorem list_image_covers_range {A : Type} (items : List A) (map : A → Nat) (bound : Nat)
    (distinct : (items.map map).Nodup)
    (bounded : ∀ item ∈ items, map item < bound) (length : items.length = bound) :
    ∀ index : Nat, index < bound → ∃ item ∈ items, map item = index := by
  classical
  intro index inside
  apply Classical.byContradiction
  intro missing
  have absent : index ∉ items.map map := by
    intro member
    obtain ⟨item,inItems,equal⟩ := List.mem_map.mp member
    exact missing ⟨item,inItems,equal⟩
  have subset : items.map map ⊆ (List.range bound).erase index := by
    intro value member
    obtain ⟨item,inItems,rfl⟩ := List.mem_map.mp member
    apply (List.mem_erase_of_ne ?_).mpr (List.mem_range.mpr (bounded item inItems))
    intro equal
    apply absent
    exact List.mem_map.mpr ⟨item,inItems,equal⟩
  have shorter := distinct.length_le_of_subset subset
  have erased := List.length_erase_of_mem (List.mem_range.mpr inside)
  rw [List.length_map,length,erased,List.length_range] at shorter
  omega

#print axioms list_nodup_map_of_injective_on
#print axioms list_image_covers_range
end InitECandidate.Runtime
