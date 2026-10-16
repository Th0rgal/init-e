import InitECandidate.Runtime.PanCrepEntryClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang

private theorem list_lookup_isSome_iff {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) : (List.lookup k l).isSome = true ↔ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    by_cases h : k = a
    · subst h; simp
    · have : (k == a) = false := by simp [h]
      simp [List.lookup_cons, this, ih, h]

/-- Membership of a key/value pair in a list with distinct keys determines
    `List.lookup`. -/
private theorem fupdateList_empty_eq_lookup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) :
    FUPDATE_LIST FEMPTY l k = List.lookup k l.reverse := by
  have := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup l.reverse k
  simpa [FLOOKUP] using this

/-- The right-folded `alist_to_fmap` is `List.lookup`. -/
private theorem alistToFmap_eq_lookup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) : FLOOKUP (alistToFmap l) k = List.lookup k l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    change FLOOKUP (FUPDATE (alistToFmap l) (a, b)) k = _
    rw [FLOOKUP_update, ih, List.lookup_cons]
    by_cases hk : k = a
    · subst hk; simp
    · have h1 : (a == k) = false := by simp [Ne.symm hk]
      have h2 : (k == a) = false := by simp [hk]
      simp [h1, h2]

/-- Exception-shape installation and compiler exception-ID allocation have
identical domains, with the original update order and finite-map semantics. -/
theorem pan_exception_table_domain {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) (key : MlS) :
    ((HolFiniteMapExact.empty.updateList (exceptionsHOL code)).lookup key).isSome =
      ((getEidsFromDeclsHOL code).lookup key).isSome := by
  rw [HolFiniteMapExact.lookup_updateList,holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL,
    alistToFmap_eq_lookup]
  change (FUPDATE_LIST FEMPTY _ key).isSome = _
  rw [fupdateList_empty_eq_lookup]
  apply Bool.eq_iff_iff.mpr
  rw [list_lookup_isSome_iff,list_lookup_isSome_iff,List.map_reverse,List.mem_reverse,
    getEidsEntriesHOL_eq_lengthBased]
  simp only
  rw [List.map_fst_zip (by simp)]

#print axioms pan_exception_table_domain
end InitECandidate.Runtime
