import InitECandidate.Runtime.SourceCostLoopLiveCallG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-- A complete return tuple writes every named destination. -/
theorem live_zip_absentG {α : Type} (names : List Nat) (values : List α) (key : Nat)
    (lengths : names.length = values.length)
    (absent : holAlookup (names.zip values) key = none) : key ∉ names := by
  induction names generalizing values with
  | nil => simp
  | cons head tail ih =>
    cases values with
    | nil => simp at lengths
    | cons value rest =>
      simp only [List.zip_cons_cons, holAlookup] at absent
      split at absent
      · cases absent
      · rename_i different
        simp only [List.mem_cons, not_or]
        exact ⟨fun same => different same.symm, ih rest (by simpa using lengths) absent⟩

/-- Returning values extend a saved caller footprint by the returned names.
The only old bindings needed are live names not overwritten by the return. -/
theorem live_projection_returnG {α : Type} (source target : Spt α)
    (names : List Nat) (values : List α) (live : NumSet)
    (lengths : names.length = values.length)
    (input : sptSubspt (sptInter source (sptListDelete names live)) target) :
    sptSubspt (sptInter (sptAlistInsert names values source) live)
      (sptAlistInsert names values target) := by
  intro key member
  obtain ⟨present, needed⟩ := (live_mem_interG _ live key).mp member
  have lookupEq : sptLookup key (sptAlistInsert names values target) =
      sptLookup key (sptAlistInsert names values source) := by
    rw [lookup_alist_insert_any, lookup_alist_insert_any]
    cases absent : holAlookup (names.zip values) key with
    | some value => rfl
    | none =>
      have notNamed := live_zip_absentG names values key lengths absent
      have oldPresent : sptMem key source := by
        simpa only [sptMem, sptDomain, lookup_alist_insert_any, absent] using present
      have notWritten : sptMem key (sptListDelete names live) :=
        (sptDomain_sptListDelete names live key).mpr ⟨needed, notNamed⟩
      have pair := input key ((live_mem_interG _ _ key).mpr ⟨oldPresent, notWritten⟩)
      simpa only [sptLookup_sptInter,
        if_pos (show (sptLookup key (sptListDelete names live)).isSome = true from notWritten)] using pair.2
  refine ⟨?_, ?_⟩
  · simpa only [sptMem, sptDomain, lookupEq] using present
  · rw [sptLookup_sptInter,
      if_pos (show (sptLookup key live).isSome = true from needed)]
    exact lookupEq

/-- Exception binding is a one-word ownership extension of saved caller locals. -/
theorem live_projection_exceptionG {α : Type} (source target : Spt α)
    (name : Nat) (value : α) (live : NumSet)
    (input : sptSubspt (sptInter source (sptDelete name live)) target) :
    sptSubspt (sptInter (sptInsert name value source) live) (sptInsert name value target) := by
  have one : sptListDelete [name] live = sptDelete name live := rfl
  simpa only [sptAlistInsert] using
    live_projection_returnG source target [name] [value] live rfl (by simpa only [one] using input)

#print axioms live_projection_returnG
#print axioms live_projection_exceptionG
end InitECandidate.Runtime.FineCost
