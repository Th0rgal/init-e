import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- Leaving a temporary scope retains an update to a distinct caller local. -/
theorem restore_updated_other_local {A B : Type} [BEq A] [LawfulBEq A] [DecidableEq A]
    (locals : HolFiniteMapExact A B) (name other : A) (value next : B) (different : name ≠ other) :
    HolFiniteMapExact.resVarEq ((locals.update (name,value)).update (other,next))
      (name,locals.lookup name) = locals.update (other,next) := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases same : key = name
  · subst key
    cases saved : locals.lookup name <;>
      simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_update,HolFiniteMapExact.lookup_updateEq,
        HolFiniteMapExact.lookup_eraseEq,FUPDATE,FUPDATE_HOL,FDOMSUB_HOL,saved,different,Ne.symm different]
  · have backwards : name ≠ key := Ne.symm same
    cases saved : locals.lookup name <;>
      simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_update,HolFiniteMapExact.lookup_updateEq,
        HolFiniteMapExact.lookup_eraseEq,FUPDATE,FUPDATE_HOL,FDOMSUB_HOL,same,backwards]

#print axioms restore_updated_other_local
end InitECandidate.Runtime
