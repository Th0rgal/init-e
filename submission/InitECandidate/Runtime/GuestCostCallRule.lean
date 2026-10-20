import InitECandidate.Runtime.GuestCostWorkScore
import InitECandidate.Runtime.PanCallCostPlan
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

variable {F : Type}

abbrev CallEventInfo := Option (Option (VarKind × MlStringHOL) ×
  Option (MlStringHOL × MlStringHOL × ProgHOL 64))

/-- Canonical executed event list of one installed call statement: the call
entry, the actual argument expressions that were evaluated, the actual
argument words and frame slots, the return slots the compiler zero-initializes
for the callee's declared return shape, the traced callee body, and the actual
returned result words. -/
noncomputable def callEvents {F : Type} (s : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (returnShape : ShapeHOL)
    (bodyResult : Option (PanSemResultExact 64))
    (bodyEvents : List WorkEvent) (info : CallEventInfo := none) : List WorkEvent :=
  .statement :: (expressionListEvents s arguments ++
    [.copy (values.flatMap flattenHOL).length, .frame values.length,
      .frame (sizeOfShapeWithContextHOL s.structs returnShape)] ++ bodyEvents ++
    [.copy (callPayloadWords bodyResult)] ++ callGlobalEvents info bodyResult)

/-- Local scalar cost of one executed call: statement entry, the actual argument
expressions, the actual argument words, frame slots, the traced callee body, and
the returned words. Every term is a coefficient times an actual size; no
whole-program maximum appears. -/
noncomputable def callLocalCost {F : Type} (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (returnShape : ShapeHOL)
    (bodyResult : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent)
    (info : CallEventInfo := none) : Nat :=
  coeff.statements + coeff.score (executionWork (expressionListEvents s arguments)) +
    coeff.movedWords * (values.flatMap flattenHOL).length + coeff.frameSlots * values.length +
    coeff.frameSlots * sizeOfShapeWithContextHOL s.structs returnShape +
    coeff.score (executionWork bodyEvents) + coeff.movedWords * callPayloadWords bodyResult +
    coeff.score (executionWork (callGlobalEvents info bodyResult))

/-- The recorded events of one call score exactly its local cost. -/
theorem callEvents_score {F : Type} (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (returnShape : ShapeHOL)
    (bodyResult : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent)
    (info : CallEventInfo := none) :
    coeff.score (executionWork
        (callEvents s arguments values returnShape bodyResult bodyEvents info)) =
      callLocalCost coeff s arguments values returnShape bodyResult bodyEvents info := by
  unfold callEvents callLocalCost
  rw [executionWork_score_cons, score_statement]
  simp only [executionWork_score_append]
  simp only [executionWork_score_cons, score_frame, guest_score_copy, score_singleton, score_pair,
    executionWork_nil_score]
  omega

/-- Actual installed call statement: the exact trace from `StatementRun.callDone`
together with its local cost, which is only the statement entry, the evaluated
arguments, the actual word moves and frame slots, the traced callee body, and the
returned payload words. -/
theorem call_statement_work {F : Type} (coeff : Work) {s : PanSemStateFiniteExact 64 F}
    {info : Option (Option (VarKind × MlStringHOL) × Option (MlStringHOL × MlStringHOL × ProgHOL 64))}
    {function : MlStringHOL} {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {returnShape : ShapeHOL} {bodyResult : Option (PanSemResultExact 64)}
    {bodyPost : PanSemStateFiniteExact 64 F} {bodyEvents : List WorkEvent}
    {result : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post) :
    StatementRun s (.call info function arguments) result post
      (callEvents s arguments values returnShape bodyResult bodyEvents info) ∧
    coeff.score (executionWork
        (callEvents s arguments values returnShape bodyResult bodyEvents info)) =
      callLocalCost coeff s arguments values returnShape bodyResult bodyEvents info := by
  refine ⟨?_, callEvents_score coeff s arguments values returnShape bodyResult bodyEvents info⟩
  have run := StatementRun.callDone (s := s) (info := info) (function := function)
    (arguments := arguments) (values := values) (body := body) (callee := callee)
    (returnShape := returnShape) (bodyResult := bodyResult) (bodyPost := bodyPost)
    (bodyEvents := bodyEvents) (result := result) (post := post)
    args lookup clock bodyRun plan
  unfold callEvents
  exact run

#print axioms callEvents_score
#print axioms call_statement_work
end InitECandidate.Runtime.FineCost
