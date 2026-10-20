import InitECandidate.Runtime.PanTotalExpressionCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Pure call-exit dispatch exposes the only possible recursive continuation:
a matched exception handler. It cannot hide callee or handler execution. -/
inductive CallCostPlan (F : Type) where
  | done (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F)
  | handler (entry : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)

noncomputable def callCostPlan {F : Type} (s : PanSemStateFiniteExact 64 F)
    (info : Option (Option (VarKind × MlStringHOL) ×
      Option (MlStringHOL × MlStringHOL × ProgHOL 64)))
    (returnShape : ShapeHOL) (result : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F) : CallCostPlan F := by
  classical
  exact match result with
  | none | some .break | some .continue => .done (some .error) post
  | some (.returned value) =>
      if shapeEqHOL (shapeOfHOLExact value) returnShape then
        match info with
        | none => .done (some (.returned value)) (emptyLocalsHOLFinite post)
        | some (none, _) => .done none { post with locals := s.locals }
        | some (some (kind, name), _) =>
            if isValidValueHOLExact s.toExact kind name value then
              .done none (setKvarHOLFinite kind name value { post with locals := s.locals })
            else .done (some .error) post
      else .done (some .error) post
  | some (.exception exceptionId value) =>
      match info with
      | none | some (_, none) =>
          .done (some (.exception exceptionId value)) (emptyLocalsHOLFinite post)
      | some (_, some (handlerId, handlerVar, program)) =>
          if exceptionId = handlerId then
            match s.eshapes.lookup exceptionId with
            | some shape =>
                if shapeEqHOL (shapeOfHOLExact value) shape &&
                    isValidValueHOLExact s.toExact .local handlerVar value then
                  .handler (setVarHOLFinite handlerVar value { post with locals := s.locals }) program
                else .done (some .error) post
            | none => .done (some .error) post
          else .done (some (.exception exceptionId value)) (emptyLocalsHOLFinite post)
  | some other => .done (some other) (emptyLocalsHOLFinite post)

noncomputable def evaluateCallCostPlan {F : Type} : CallCostPlan F →
    Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F
  | .done result post => (result, post)
  | .handler entry program => evaluateHOLFiniteState entry program

/-- Exact dispatch decomposition, retaining actual argument evaluation,
lookup, clock guard and callee evaluation. This is not a whole-call run premise. -/
theorem evaluate_call_cost_plan {F : Type} (s : PanSemStateFiniteExact 64 F)
    (info) (function : MlStringHOL) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F)
    (args : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (result, post)) :
    evaluateHOLFiniteState s (.call info function arguments) =
      evaluateCallCostPlan (callCostPlan s info returnShape result post) := by
  rw [evaluateHOLFiniteState_call]
  simp only [args, lookup, clock, ↓reduceIte, run]
  cases result with
  | none => rfl
  | some result =>
    cases result <;> simp only [callCostPlan]
    all_goals repeat' split
    all_goals simp_all [evaluateCallCostPlan]

def callPayloadWords : Option (PanSemResultExact 64) → Nat
  | some (.returned value) | some (.exception _ value) => (flattenHOL value).length
  | _ => 0

def declareCallStopPlan {F : Type} (result : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F) : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F :=
  match result with
  | none | some .break | some .continue => (some .error, post)
  | some other => (some other, emptyLocalsHOLFinite post)

#print axioms evaluate_call_cost_plan
end InitECandidate.Runtime.FineCost
