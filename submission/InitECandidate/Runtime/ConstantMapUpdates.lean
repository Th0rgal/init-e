import Flapjack.Pancake.Semantics.CrepSem.HOLState
namespace InitECandidate.Runtime
open Flapjack

/-- Updating any list of keys to a common value needs no uniqueness assumption. -/
theorem constant_updates_lookup {A B : Type} [BEq A] [LawfulBEq A] [DecidableEq A]
    (keys : List A) (map : HolFiniteMapExact A B) (value : B) (key : A) :
    (keys.foldl (fun current name => current.update (name,value)) map).lookup key =
      if key ∈ keys then some value else map.lookup key := by
  induction keys generalizing map with
  | nil => simp
  | cons name keys ih =>
    rw [List.foldl_cons,ih]
    by_cases member : key ∈ keys
    · simp [member]
    · by_cases equal : key = name
      · subst equal
        simp [member,HolFiniteMapExact.lookup_update,FUPDATE]
      · have different : name ≠ key := Ne.symm equal
        simp [member,equal,different,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms constant_updates_lookup
end InitECandidate.Runtime
