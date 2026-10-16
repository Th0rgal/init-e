import InitECandidate.Runtime.GasFrameExpressions

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Lift an exact code lookup back to its canonical finite-map carrier. -/
theorem lookupCodeFinite_of_exact (code : MlS → Option
      (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (arguments : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (h : lookupCodeHOLExact code name arguments = some (body, callee.lookup, shape)) :
    lookupCodeHOLFinite code name arguments = some (body, callee, shape) := by
  cases result : lookupCodeHOLFinite code name arguments with
  | none =>
    have missing := (lookupCodeHOLFinite_eq_none_iff code name arguments).mp result
    rw [h] at missing
    cases missing
  | some entry =>
    rcases entry with ⟨actualBody, actualCallee, actualShape⟩
    have actual := lookupCodeHOLFinite_eq_some code name arguments actualBody actualCallee actualShape result
    have pieces : body = actualBody ∧ callee.lookup = actualCallee.lookup ∧ shape = actualShape := by
      simpa only [Prod.mk.injEq] using Option.some.inj (h.symm.trans actual)
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨pieces.1.symm, (HolFiniteMapExact.ext pieces.2.1).symm, pieces.2.2.symm⟩

def minCalleeLocals (left right : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "a", .val (.word left))).update
    (ofString "b", .val (.word right))

def minCodeEntry : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  ([(ofString "a", .one), (ofString "b", .one)], sourceFunctionBody Guest.guestFn_min, .one)

theorem lookup_source_min (code : MlS → Option
      (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (left right : BitVec 64) (installed : code (ofString "min") = some minCodeEntry) :
    lookupCodeHOLFinite code (ofString "min") [.val (.word left), .val (.word right)] =
      some (sourceFunctionBody Guest.guestFn_min, minCalleeLocals left right, .one) := by
  apply lookupCodeFinite_of_exact
  have names : ofString "a" ≠ ofString "b" := by decide_cbv
  simp [lookupCodeHOLExact, installed, minCodeEntry, shapeOfHOLExact, shapeEqHOL, names]
  funext current
  by_cases hb : current = ofString "b"
  · subst current; simp [minCalleeLocals, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]
  · by_cases ha : current = ofString "a"
    · subst current; simp [minCalleeLocals, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE, hb, Ne.symm hb]
    · simp [minCalleeLocals, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE, hb, ha, Ne.symm hb, Ne.symm ha]

theorem minCalleeLocals_left (left right : BitVec 64) :
    (minCalleeLocals left right).lookup (ofString "a") = some (.val (.word left)) := by
  have names : ofString "b" ≠ ofString "a" := by decide_cbv
  simp [minCalleeLocals, HolFiniteMapExact.update, FUPDATE, names]

theorem minCalleeLocals_right (left right : BitVec 64) :
    (minCalleeLocals left right).lookup (ofString "b") = some (.val (.word right)) := by
  simp [minCalleeLocals, HolFiniteMapExact.update, FUPDATE]

/-- Executing the installed helper consumes exactly one source clock unit.
The continuation is left explicit so this summary applies to every caller. -/
theorem evaluate_min_decCall {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (left right : BitVec 64)
    (installed : state.code.lookup (ofString "min") = some minCodeEntry)
    (args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word left), .val (.word right)])
    (clock : state.clock ≠ 0) :
    evaluateHOLFiniteState state (.decCall name .one (ofString "min") arguments continuation) =
      let next := setVarHOLFinite name (.val (.word (wordMin left right)))
        { state with clock := state.clock - 1 }
      let output := evaluateHOLFiniteState next continuation
      (output.1, { output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
        (name, state.locals.lookup name)) }) := by
  classical
  have body := evaluate_source_min (callEntryStateHOLFinite state (minCalleeLocals left right))
    left right (minCalleeLocals_left left right) (minCalleeLocals_right left right)
  rw [evaluateHOLFiniteState_decCall_total, args]
  dsimp only
  rw [lookup_source_min state.code.lookup left right installed]
  simp only [clock, ↓reduceIte]
  rw [fixClockHOLFinite_evaluateState, body]
  simp [shapeOfHOLExact, shapeEqHOL, callEntryStateHOLFinite, emptyLocalsHOLFinite]

#print axioms evaluate_min_decCall

end InitECandidate.Runtime
