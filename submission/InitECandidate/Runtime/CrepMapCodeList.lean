import InitECandidate.Runtime.CrepEntryCeiling
namespace InitECandidate.Runtime
open Flapjack

theorem map2_updateList {α β γ : Type} [BEq α] [LawfulBEq α]
    (f : α × β → γ) (code : HolFiniteMapExact α β) (entries : List (α × β)) :
    (code.updateList entries).map2 f =
      (code.map2 f).updateList (entries.map (fun entry => (entry.1,f entry))) := by
  induction entries generalizing code with
  | nil => rfl
  | cons entry rest ih =>
    have outer : code.updateList (entry :: rest) = (code.update entry).updateList rest := by
      apply HolFiniteMapExact.ext
      funext key
      rfl
    have step : (code.update entry).map2 f = (code.map2 f).update (entry.1,f entry) := by
      apply HolFiniteMapExact.ext
      funext key
      simp only [HolFiniteMapExact.lookup_map2,HolFiniteMapExact.lookup_update]
      unfold FUPDATE
      by_cases equal : entry.1 = key
      · subst key
        simp
      · simp [equal]
    rw [outer,ih,step]
    rfl

#print axioms map2_updateList
end InitECandidate.Runtime
