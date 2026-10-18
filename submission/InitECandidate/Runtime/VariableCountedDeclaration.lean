import InitECandidate.Runtime.VariableCountedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The original declaration form with a runtime local limit, uniformly over
all states. Missing or nonword limits reject; negative signed limits skip. -/
theorem ProgBounded.variableCountedDec (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true) (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const (0#64))
      (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  let entered := setVarHOLFinite counter (.val (.word (0#64))) state
  have atCounter : entered.locals.lookup counter = some (.val (.word (0#64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  let loop := ProgHOL.while (.cmp op (.var .local counter) (.var .local limit)) body
  have loopBound : entered.clock ≤ (evaluateHOLFiniteState entered loop).2.clock +
        (2 ^ 64 - 1) * (cost + 1) ∧
      (evaluateHOLFiniteState entered loop).2.clock ≤ entered.clock ∧
      (evaluateHOLFiniteState entered loop).1 ≠ some .timeOut := by
    cases lookup : entered.locals.lookup limit with
    | none =>
      have condition : evalHOLFinite entered
          (h := fun a => Classical.propDecidable (entered.memaddrs a))
          (.cmp op (.var .local counter) (.var .local limit)) = none := by
        simp [evalHOLFinite_eq_toExact,evalHOLExact,atCounter,lookup]
      dsimp only [loop]
      rw [evaluateHOLFiniteState_while_total,condition]
      simp
    | some value =>
      cases value with
      | val word =>
        cases word with
        | word K =>
          exact variableCountedWhile_zero_bounded counter limit op hop counted preservesLimit
            entered code K atCounter lookup (by change _ ≤ state.clock; omega)
      | rStruct fields =>
        have condition : evalHOLFinite entered
            (h := fun a => Classical.propDecidable (entered.memaddrs a))
            (.cmp op (.var .local counter) (.var .local limit)) = none := by
          simp [evalHOLFinite_eq_toExact,evalHOLExact,atCounter,lookup]
        dsimp only [loop]
        rw [evaluateHOLFiniteState_while_total,condition]
        simp
      | nStruct name fields =>
        have condition : evalHOLFinite entered
            (h := fun a => Classical.propDecidable (entered.memaddrs a))
            (.cmp op (.var .local counter) (.var .local limit)) = none := by
          simp [evalHOLFinite_eq_toExact,evalHOLExact,atCounter,lookup]
        dsimp only [loop]
        rw [evaluateHOLFiniteState_while_total,condition]
        simp
  have meta' := evaluateHOLFiniteState_metadata entered loop
  change state.clock ≤ (evaluateHOLFiniteState entered (.seq loop tail)).2.clock + _ ∧
    (evaluateHOLFiniteState entered (.seq loop tail)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState entered (.seq loop tail)).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered loop with
  | mk result middle =>
    rw [loopRun] at loopBound meta'
    dsimp only at loopBound meta'
    obtain ⟨spent,kept,safe⟩ := loopBound
    change state.clock ≤ middle.clock + (2 ^ 64 - 1) * (cost + 1) at spent
    change middle.clock ≤ state.clock at kept
    cases result with
    | none =>
      dsimp only
      obtain ⟨t1,t2,t3⟩ := rest middle (meta'.1.trans code) (by omega)
      exact ⟨by omega,by omega,t3⟩
    | some r =>
      dsimp only
      exact ⟨by omega,kept,safe⟩

/-- Assignment-initialized variant used by the second and later array loops
in original functions such as payload hashing. -/
theorem ProgBounded.variableCountedAssign (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) {body tail : ProgHOL 64} {cost tailCost : Nat}
    (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true) (rest : ProgBounded tail tailCost) :
    ProgBounded (.seq (.assign .local counter (.const (0#64)))
      (.seq (.while (.cmp op (.var .local counter) (.var .local limit)) body) tail))
      ((2 ^ 64 - 1) * (cost + 1) + tailCost) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word (0#64))) = true
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const (0#64))) =
        (none,setKvarHOLFinite .local counter (.val (.word (0#64))) state) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,valid]
    rw [evaluateHOLFiniteState_seq_line780,assignRun]
    dsimp only
    have declared := ProgBounded.variableCountedDec counter limit op hop counted preservesLimit rest
      state code budget
    rw [evaluateHOLFiniteState_dec_total] at declared
    simpa only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true,setKvarHOLFinite] using declared
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const (0#64))) =
        (some .error,state) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,valid]
    rw [evaluateHOLFiniteState_seq_line780,assignRun]
    simp

#print axioms ProgBounded.variableCountedDec
#print axioms ProgBounded.variableCountedAssign
end InitECandidate.Runtime
