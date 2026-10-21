import InitECandidate.Runtime.GuestCostOpPopBody
import InitECandidate.Runtime.GuestCostOpAddLookup
import InitECandidate.Runtime.GuestFrameInvariant
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

/-- Reusable `decCall` continuation step: a checked callee body run plus a checked
continuation run compose into the declared-call statement. This is the wrapper
needed by every opcode whose spine starts with `decCall x stack_pop []`. -/
theorem StatementRun.declareCallReturn_cont
    {s : PanSemStateFiniteExact 64 F} {name : MlStringHOL} {shape : ShapeHOL}
    {function : MlStringHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {returnShape : ShapeHOL}
    {value : ValueHOL 64} {bodyPost : PanSemStateFiniteExact 64 F}
    {bodyEvents : List WorkEvent} {result : Option (PanSemResultExact 64)}
    {post : PanSemStateFiniteExact 64 F} {continuationEvents : List WorkEvent}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values =
      some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body
      (some (.returned value)) bodyPost bodyEvents)
    (shapeMatch : (shapeEqHOL (shapeOfHOLExact value) shape &&
      shapeEqHOL (shapeOfHOLExact value) returnShape) = true)
    (continuationRun : StatementRun
      (setVarHOLFinite name value { bodyPost with locals := s.locals })
      continuation result post continuationEvents) :
    StatementRun s (.decCall name shape function arguments continuation) result
      { post with locals := HolFiniteMapExact.resVarEq post.locals (name, s.locals.lookup name) }
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs shape))] ++ bodyEvents ++
        [.cost (returnCopy (flattenHOL value).length)] ++ continuationEvents)) :=
  StatementRun.declareCallReturn args lookup clock bodyRun shapeMatch continuationRun

/-- Frame offsets 0 and 64 are distinct, so `charge_gas` preserves the pc cell. -/
theorem frame_add_zero_ne_64 (frame : BitVec 64) :
    frame + (64 : BitVec 64) ≠ frame + 0 := by bv_omega

/-- Frame offsets 0 and 184 are distinct, so `charge_gas` preserves the pc cell. -/
theorem frame_add_zero_ne_184 (frame : BitVec 64) :
    frame + (184 : BitVec 64) ≠ frame + 0 := by bv_omega

#print axioms frame_add_zero_ne_64
#print axioms frame_add_zero_ne_184

#print axioms StatementRun.declareCallReturn_cont
end InitECandidate.Runtime.FineCost
