import InitECandidate.Runtime.SourceCostGlobalsRunAtomic
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

theorem globals_address_events (B : Nat) {F : Type} {t : PanSemStateFiniteExact 64 F} {address : BitVec 64}
    {value : Option (ValueHOL 64)} {ev : List WorkEvent}
    (run : CostedExpressionRun t (.op .sub [.topAddr, .const address]) value ev) :
    sharpSourceScore B ev = globalAddressPrice srcK := by
  rw [run.events_eq]; exact globals_address_score B t address

theorem globals_valid_global {F : Type} {s : PanSemStateFiniteExact 64 F} {name} {value : ValueHOL 64}
    (valid : isValidValueHOLFinite s .global name value = true) :
    ∃ old, s.globals.lookup name = some old := by
  simp only [isValidValueHOLFinite, lookupKvarHOLFinite] at valid
  split at valid
  · exact ⟨_, ‹_›⟩
  · simp at valid

/-- A global assignment becomes a `TopAddr` store: its address (`globalAddressPrice`), memory
words and replay are paid by the source copy and `globalAccess` event. -/
theorem globals_assignGlobal (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name} {expression : ExpHOL 64} {value : ValueHOL 64} {events : List WorkEvent}
    (expr : CostedExpressionRun s expression (some value) events)
    (valid : isValidValueHOLFinite s .global name value = true) :
    GlobalsLe fn B s (.assign .global name expression) none (setKvarHOLFinite .global name value s)
      (.statement :: (events ++ .copy (flattenHOL value).length ::
        globalEvents .global (flattenHOL value).length)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.assignValue expr valid) ok rel target
  obtain ⟨old, hold⟩ := globals_valid_global valid
  obtain ⟨address, found, _⟩ := globalsRel_global rel hold
  have compiled : compileProgExactHOL context (.assign .global name expression) =
      .store (.op .sub [.topAddr, .const address]) (compileExpExactHOL context expression) := by
    simp [compileProgExactHOL, found]
  rw [compiled] at target
  cases target
  case storeValue =>
    obtain ⟨hv, a⟩ := globals_costed B rel expr (by assumption) ready
    cases hv
    have addr := globals_address_events B
      (by assumption : CostedExpressionRun t (.op .sub [.topAddr, .const address]) _ _)
    simp only [globalEvents] at *
    gsimp
    simp only [globalAddressPrice, srcK_top, srcK_cst, srcK_op] at addr
    omega
  all_goals cases hr

theorem globals_primitiveValue (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name operator} {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)} {value : ValueHOL 64}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (operation : panPrimopHOLExact operator values = some value)
    (valid : isValidValueHOLFinite s .local name value = true) :
    GlobalsLe fn B s (.primitive name operator arguments) none (setVarHOLFinite name value s)
      (.statement :: (expressionListEvents s arguments ++ [.cost (primitiveOverhead (values.flatMap flattenHOL).length)] ++
        [.copy (flattenHOL value).length])) := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.primitiveValue args operation valid) ok rel target
  have values' := globals_list_values rel arguments values args
  have listLe := globals_list_le B rel arguments ready (by
    show evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments ≠ none
    rw [args]; simp)
  simp only [compileProgExactHOL] at target
  cases target
  case primitiveValue =>
    rename_i vs v _ operation' args'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    rw [operation] at operation'
    cases operation'
    gsimp
    omega
  all_goals cases hr

#print axioms globals_assignGlobal
#print axioms globals_primitiveValue
end InitECandidate.Runtime.FineCost
