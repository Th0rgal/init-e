import InitECandidate.Runtime.SourceCostLoopTop
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Post-declaration facts of the pinned `pan_to_crep` declaration proof
(its private helpers, restated). -/

/-- `List.lookup` distinguishes membership in the key list. -/
theorem pipeline_list_lookup_isSome_iff {α β : Type} [BEq α] [LawfulBEq α]
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
theorem pipeline_list_lookup_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α]
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
theorem pipeline_list_lookup_mem {α β : Type} [BEq α] [LawfulBEq α]
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
theorem pipeline_list_lookup_reverse_of_nodup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (hnd : (l.map Prod.fst).Nodup) :
    List.lookup k l.reverse = List.lookup k l := by
  have hnd' : (l.reverse.map Prod.fst).Nodup := by
    rw [List.map_reverse, List.Nodup, List.pairwise_reverse]; exact hnd.imp (fun h => Ne.symm h)
  cases h : List.lookup k l with
  | none =>
    cases h' : List.lookup k l.reverse with
    | none => rfl
    | some v =>
      have hm := pipeline_list_lookup_mem _ _ _ h'
      have := pipeline_list_lookup_of_mem_nodup l k v (List.mem_reverse.mp hm) hnd
      rw [h] at this; cases this
  | some v =>
    exact pipeline_list_lookup_of_mem_nodup _ k v (List.mem_reverse.mpr (pipeline_list_lookup_mem _ _ _ h)) hnd'

/-- `FUPDATE_LIST FEMPTY` of a list is `List.lookup` on its reverse. -/
theorem pipeline_fupdateList_empty_eq_lookup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) :
    FUPDATE_LIST FEMPTY l k = List.lookup k l.reverse := by
  have := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup l.reverse k
  simpa [FLOOKUP] using this

/-- The right-folded `alist_to_fmap` is `List.lookup`. -/
theorem pipeline_alistToFmap_eq_lookup {α β : Type} [BEq α] [LawfulBEq α]
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


theorem pipeline_code_reverse (code : List (DeclHOL 64))
    (distinct : ((functionsHOL code).map Prod.fst).Nodup) :
    HolFiniteMapExact.empty.updateList (functionsHOL code) =
      HolFiniteMapExact.empty.updateList (functionsHOL code).reverse := by
  apply HolFiniteMapExact.ext
  funext k
  simp only [HolFiniteMapExact.lookup_updateList]
  change FUPDATE_LIST FEMPTY _ k = FUPDATE_LIST FEMPTY _ k
  rw [pipeline_fupdateList_empty_eq_lookup, pipeline_fupdateList_empty_eq_lookup, List.reverse_reverse,
    pipeline_list_lookup_reverse_of_nodup _ _ distinct]

theorem pipeline_eids_domain (code : List (DeclHOL 64)) (key : MlS) :
    ((HolFiniteMapExact.empty.updateList (exceptionsHOL code)).lookup key).isSome =
      ((getEidsFromDeclsHOL code).lookup key).isSome := by
  rw [HolFiniteMapExact.lookup_updateList, holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL,
    pipeline_alistToFmap_eq_lookup]
  change (FUPDATE_LIST FEMPTY _ key).isSome = _
  rw [pipeline_fupdateList_empty_eq_lookup]
  apply Bool.eq_iff_iff.mpr
  rw [pipeline_list_lookup_isSome_iff, pipeline_list_lookup_isSome_iff, List.map_reverse, List.mem_reverse,
    getEidsEntriesHOL_eq_lengthBased]
  simp only
  rw [List.map_fst_zip (by simp)]

/-- The generated entry is the first compiled function, with no parameters. -/
theorem pipeline_start_lookup (code : List (DeclHOL 64)) (main : MlS) (body : ProgHOL 64)
    (rshape : ShapeHOL) (hl : List.lookup main (functionsHOL code) = some ([], body, rshape)) :
    ∃ program, holAlookup (compileProgDeclsHOLW (compileTopExactHOL code main)) main =
      some ([], program) := by
  have hfun : ∃ b' rest, functionsHOL (compileTopExactHOL code main) =
      (main, [], b', rshape) :: rest := by
    unfold compileTopExactHOL
    rw [compileTopFunctionLookup_eq_lookup, hl]
    simp only
    rw [PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL _ _ _ _ _ _ rfl,
      functionsHOL_append, functionsFilterNilHOL]
    exact ⟨_, _, rfl⟩
  obtain ⟨b', rest, hf⟩ := hfun
  simp only [compileProgDeclsHOLW, compileToCrepExactHOLW, hf, List.map_cons,
    CrepInlineCanonical.compileInlTopHOLExact, CrepInlineCanonical.compileInlProgHOLExactWithSupport]
  simp [holAlookup, crepVarsHOL, sizeOfShapeHOL]

#print axioms pipeline_start_lookup
#print axioms pipeline_code_reverse
#print axioms pipeline_eids_domain
end InitECandidate.Runtime.FineCost
