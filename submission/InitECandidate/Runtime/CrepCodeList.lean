import InitECandidate.Runtime.CrepFiniteCode
namespace InitECandidate.Runtime
open Flapjack
open Flapjack.Basis.Pure.MlString

/-- An explicit ceiling for a concrete list of generated Crep procedures. -/
noncomputable def crepCodeListLimit {width : Nat} [NeZero width]
    (entries : List (MlString × List Nat × CrepProgHOL width)) : Nat :=
  (entries.map (fun entry => sizeOf entry.2.2)).sum

private theorem entry_size_le {width : Nat} [NeZero width]
    (entries : List (MlString × List Nat × CrepProgHOL width))
    (entry : MlString × List Nat × CrepProgHOL width) (member : entry ∈ entries) :
    sizeOf entry.2.2 ≤ crepCodeListLimit entries := by
  induction entries with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    simp only [crepCodeListLimit,List.map_cons,List.sum_cons]
    rcases member with equal | member
    · subst entry; omega
    · have := ih member; unfold crepCodeListLimit at this; omega

private theorem updates_bounded {width : Nat} [NeZero width]
    (limit : Nat) (entries : List (MlString × List Nat × CrepProgHOL width))
    (code : FiniteMap MlString (List Nat × CrepProgHOL width))
    (hc : ∀ name params body, code name = some (params,body) → sizeOf body ≤ limit)
    (he : ∀ entry ∈ entries, sizeOf entry.2.2 ≤ limit) :
    ∀ name params body, FUPDATE_LIST code entries name = some (params,body) → sizeOf body ≤ limit := by
  induction entries generalizing code with
  | nil => simpa only [FUPDATE_LIST,List.foldl_nil] using hc
  | cons entry rest ih =>
    intro name params body found
    rw [FUPDATE_LIST_cons] at found
    apply ih (FUPDATE code entry) ?_ (fun item member => he item (List.mem_cons_of_mem _ member)) name params body found
    intro key pars prog lookup
    unfold FUPDATE at lookup
    split at lookup
    · have same := Option.some.inj lookup
      have equal := congrArg Prod.snd same
      change entry.2.2 = prog at equal
      rw [← equal]
      exact he entry (List.mem_cons_self)
    · exact hc key pars prog lookup

/-- The original finite-map installation of a generated procedure list has
its explicit size ceiling, including repeated names and last-write lookup. -/
theorem crep_code_list_bounded {width : Nat} [NeZero width] {F : Type}
    (entries : List (MlString × List Nat × CrepProgHOL width))
    (s : CrepSemHOLState width F)
    (installed : s.code = HolFiniteMapExact.empty.updateList entries) :
    CrepCodeSize (crepCodeListLimit entries) s := by
  intro name params body found
  rw [installed,HolFiniteMapExact.lookup_updateList] at found
  exact updates_bounded _ entries HolFiniteMapExact.empty.lookup
    (by intro name params body missing; cases missing)
    (entry_size_le entries) name params body found

#print axioms crep_code_list_bounded
end InitECandidate.Runtime
