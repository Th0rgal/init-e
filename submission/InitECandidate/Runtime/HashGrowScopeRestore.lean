import InitECandidate.Runtime.HashGrowFinalAllocationSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exit nested allocation scopes using their caller's saved local bindings. -/
def restoreGrowthLocals (saved : HolFiniteMapExact MlS (ValueHOL 64)) :
    List MlS → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64)
  | [],locals => locals
  | name :: rest,locals => HolFiniteMapExact.resVarEq (restoreGrowthLocals saved rest locals) (name,saved.lookup name)

/-- Only bindings for the scopes being exited influence restoration. -/
theorem restoreGrowthLocals_congr (left right : HolFiniteMapExact MlS (ValueHOL 64))
    (names : List MlS) (agree : ∀ name ∈ names, left.lookup name = right.lookup name)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    restoreGrowthLocals left names locals = restoreGrowthLocals right names locals := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    simp only [restoreGrowthLocals]
    rw [agree name (by simp),ih (by intro key member; exact agree key (by simp [member]))]

#print axioms restoreGrowthLocals_congr
end InitECandidate.Runtime
