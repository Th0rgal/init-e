import InitECandidate.Runtime.GuestCostOpAddLookup
import InitECandidate.Runtime.GuestCostStackPush
import InitECandidate.Runtime.GuestCostU256Add
import InitECandidate.Runtime.GuestCostPcAdd
import InitECandidate.Runtime.GuestCostChargeFamily
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

set_option maxHeartbeats 4000000

/-- Explicit executed work of one returning `decCall`: the call entry, the
evaluated arguments, argument words and frame slots, the declared-shape return
slot, the traced callee body, the returned value, the traced continuation, and
the restored previous binding. -/
noncomputable def decCallEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (shape : ShapeHOL)
    (bodyEvents : List WorkEvent) (value : ValueHOL 64)
    (continuationEvents : List WorkEvent) (oldWords : Nat) : List WorkEvent :=
  .statement :: (expressionListEvents s arguments ++
    [.cost (callOverhead (values.flatMap flattenHOL).length +
      slotOverhead (sizeOfShapeWithContextHOL s.structs shape))] ++ bodyEvents ++
    [.cost (returnCopy (flattenHOL value).length)] ++ continuationEvents)

/-- Scalar cost of the same `decCall` trace: every term is a coefficient times
an actually recorded size. -/
noncomputable def decCallLocalCost {F : Type} (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (shape : ShapeHOL) (bodyEvents : List WorkEvent)
    (value : ValueHOL 64) (continuationEvents : List WorkEvent) (oldWords : Nat) : Nat :=
  coeff.score (executionWork
    (decCallEvents s arguments values shape bodyEvents value continuationEvents oldWords))

/-- A returning `decCall` executed by the actual declared call entry, with its
explicit trace and local price. -/
theorem decCall_statement_work {F : Type} (coeff : Work)
    {s : PanSemStateFiniteExact 64 F} {name : MlStringHOL} {shape : ShapeHOL}
    {function : MlStringHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {returnShape : ShapeHOL} {value : ValueHOL 64}
    {bodyPost : PanSemStateFiniteExact 64 F} {bodyEvents : List WorkEvent}
    {result : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {continuationEvents : List WorkEvent} {oldWords : Nat}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body
      (some (.returned value)) bodyPost bodyEvents)
    (shapeMatch : (shapeEqHOL (shapeOfHOLExact value) shape &&
      shapeEqHOL (shapeOfHOLExact value) returnShape) = true)
    (continuationRun : StatementRun
      (setVarHOLFinite name value { bodyPost with locals := s.locals })
      continuation result post continuationEvents)
    (oldWordsEq : oldWords = ((s.locals.lookup name).map
      (fun old => (flattenHOL old).length)).getD 0) :
    StatementRun s (.decCall name shape function arguments continuation) result
      { post with locals := HolFiniteMapExact.resVarEq post.locals (name, s.locals.lookup name) }
      (decCallEvents s arguments values shape bodyEvents value continuationEvents oldWords) ∧
    coeff.score (executionWork
        (decCallEvents s arguments values shape bodyEvents value continuationEvents oldWords)) =
      decCallLocalCost coeff s arguments values shape bodyEvents value continuationEvents oldWords := by
  refine ⟨?_, ?_⟩
  · unfold decCallEvents
    exact StatementRun.declareCallReturn (name := name) (shape := shape)
      (function := function) (arguments := arguments) (continuation := continuation)
      (values := values) (body := body) (callee := callee) (returnShape := returnShape)
      (value := value) (bodyPost := bodyPost) (bodyEvents := bodyEvents)
      (continuationEvents := continuationEvents) (result := result) (post := post)
      args lookup clock bodyRun shapeMatch continuationRun
  · rfl

/-- The pure call-exit plan of a call that discards a returned word: the caller's
locals are restored over the callee's post state. -/
theorem callCostPlan_discard_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (post : PanSemStateFiniteExact 64 F) :
    callCostPlan s (some (none, none)) .one
        (some (.returned (.val (.word (0 : BitVec 64))))) post =
      .done none { post with locals := s.locals } := by
  simp [callCostPlan, shapeOfHOLExact, shapeEqHOL]

#print axioms callCostPlan_discard_word

/-- A single local-variable argument evaluates to its bound value. -/
theorem evalListHOLFinite_singleton_var {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlStringHOL) (value : ValueHOL 64)
    (h : s.locals.lookup name = some value) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var VarKind.local name] = some [value] := by
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, h]

#print axioms evalListHOLFinite_singleton_var
#print axioms decCall_statement_work
end InitECandidate.Runtime.FineCost
