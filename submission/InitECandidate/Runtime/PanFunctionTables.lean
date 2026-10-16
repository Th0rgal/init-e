import InitECandidate.Runtime.PanDeclarationSetup
namespace InitECandidate.Runtime
open Flapjack

private theorem list_lookup_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β) (hmem : (k, v) ∈ l) (hnd : (l.map Prod.fst).Nodup) :
    List.lookup k l = some v := by
  induction l with
  | nil => simp at hmem
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with h | h
    · cases h; simp
    · have hka : k ≠ a := by
        intro hk; subst hk; exact hnd.1 (List.mem_map.mpr ⟨(k, v), h, rfl⟩)
      have : (k == a) = false := by simp [hka]
      simp [List.lookup_cons, this, ih h hnd.2]

/-- `List.lookup` returns an entry of the list. -/
private theorem list_lookup_mem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β) (h : List.lookup k l = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    by_cases hk : k = a
    · subst hk; simp at h; subst h; simp
    · have : (k == a) = false := by simp [hk]
      simp only [List.lookup_cons, this] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- With distinct keys, `List.lookup` does not depend on the list order. -/
private theorem list_lookup_reverse_of_nodup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (hnd : (l.map Prod.fst).Nodup) :
    List.lookup k l.reverse = List.lookup k l := by
  have hnd' : (l.reverse.map Prod.fst).Nodup := by
    rw [List.map_reverse, List.Nodup, List.pairwise_reverse]; exact hnd.imp (fun h => Ne.symm h)
  cases h : List.lookup k l with
  | none =>
    cases h' : List.lookup k l.reverse with
    | none => rfl
    | some v =>
      have hm := list_lookup_mem _ _ _ h'
      have := list_lookup_of_mem_nodup l k v (List.mem_reverse.mp hm) hnd
      rw [h] at this; cases this
  | some v =>
    exact list_lookup_of_mem_nodup _ k v (List.mem_reverse.mpr (list_lookup_mem _ _ _ h)) hnd'

/-- `FUPDATE_LIST FEMPTY` of a list is `List.lookup` on its reverse. -/
private theorem fupdateList_empty_eq_lookup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) :
    FUPDATE_LIST FEMPTY l k = List.lookup k l.reverse := by
  have := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup l.reverse k
  simpa [FLOOKUP] using this

/-- Unique function names make declaration-order and first-lookup installation
the same finite map. This retains the original update-list behavior. -/
theorem function_table_reverse {α β : Type} [BEq α] [LawfulBEq α]
    (entries : List (α × β)) (distinct : (entries.map Prod.fst).Nodup) :
    HolFiniteMapExact.empty.updateList entries = HolFiniteMapExact.empty.updateList entries.reverse := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateList]
  change FUPDATE_LIST FEMPTY entries key = FUPDATE_LIST FEMPTY entries.reverse key
  rw [fupdateList_empty_eq_lookup,fupdateList_empty_eq_lookup,List.reverse_reverse,
    list_lookup_reverse_of_nodup _ _ distinct]

#print axioms function_table_reverse
end InitECandidate.Runtime
