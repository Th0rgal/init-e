import InitECandidate.Runtime.GuestCostOpAddBody
import InitECandidate.Runtime.GuestCostCallRule
import InitECandidate.Runtime.OriginalArithmeticAddCode
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

def opDispatchFn : MlS := ofString "op_dispatch"

/-- Zero-argument lookup of the installed `op_add` declaration. -/
theorem opAdd_dispatch_lookup
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (installed : code = originalRuntimeCode.lookup) :
    lookupCodeHOLFinite code (ofString "op_add") [] =
      some (sourceFunctionBody Guest.guestFn_op_add, HolFiniteMapExact.empty, .one) := by
  have entry : code (ofString "op_add") =
      some ([], sourceFunctionBody Guest.guestFn_op_add, .one) := by
    rw [installed]
    exact originalRuntimeCode_opAdd_lookup
  exact pan_no_args_shape_lookup code (ofString "op_add")
    (sourceFunctionBody Guest.guestFn_op_add) .one entry

#print axioms opAdd_dispatch_lookup

/-- The dispatcher's state right after the `.call "op_add"`: the call discards
the callee result and restores the dispatcher locals. -/
noncomputable def opAddDispatchCallPost (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  { bodyPost with locals := d.locals }

/-- The dispatcher's post after the whole `op_add` arm: the trailing `return 0`
empties the locals. -/
noncomputable def opAddDispatchArmPost (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  emptyLocalsHOLFinite (opAddDispatchCallPost d bodyPost)

/-- Same trace as the dispatcher arm: the `.call` entry and frame events, the
`op_add` body events, the returned-word copy, and `return 0`. -/
noncomputable def opAddDispatchArmEvents (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent) :
    List WorkEvent :=
  callEvents opDispatchFn d (ofString "op_add") [] [] .one (some (.returned (.val (.word 0)))) bodyEvents ++
    (.statement :: (expressionEvents (opAddDispatchCallPost d bodyPost) (.const (0 : BitVec 64)) ++
      [.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length + returnMoves opDispatchFn)]))

/-- Local price of that dispatcher arm. -/
noncomputable def opAddDispatchArmLocalCost (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent) : Nat :=
  coeff.score (executionWork (opAddDispatchArmEvents d bodyPost bodyEvents))

/-- The dispatcher's `.call "op_add"` arm followed by its `return 0`, with the
call-entry, argument, frame-slot, returned-word and old-local events. -/
theorem opAdd_dispatch_arm_run (coeff : Work) (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent)
    (bodyRun : StatementRun (ofString "op_add") (callEntryStateHOLFinite d HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_op_add) (some (.returned (.val (.word 0))))
      bodyPost bodyEvents)
    (dClock : d.clock ≠ 0)
    (dInstalled : d.code.lookup = originalRuntimeCode.lookup) :
    StatementRun opDispatchFn d (.seq (.call (some (none, none)) (ofString "op_add") [])
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddDispatchArmEvents d bodyPost bodyEvents) := by
  have args : evalListHOLFinite d (h := fun a => Classical.propDecidable (d.memaddrs a)) [] =
      some [] := evalListHOLFinite_nil d
  have lookup := opAdd_dispatch_lookup d.code.lookup dInstalled
  have plan : callCostPlan d (some (none, none)) .one
      (some (.returned (.val (.word 0)))) bodyPost =
      .done none { bodyPost with locals := d.locals } :=
    callCostPlan_discard_word d bodyPost
  have callRun := (call_statement_work (coeff := coeff) (fn := opDispatchFn) args lookup dClock bodyRun plan).1
  have retRun : StatementRun opDispatchFn (opAddDispatchCallPost d bodyPost) (.return (.const (0 : BitVec 64)))
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (.statement :: (expressionEvents (opAddDispatchCallPost d bodyPost) (.const (0 : BitVec 64)) ++
        [.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length + returnMoves opDispatchFn)])) :=
    StatementRun.returnValue (fn := opDispatchFn) (expression := .const (0 : BitVec 64))
      (costedExpression_events (opAddDispatchCallPost d bodyPost) _ _
        (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  exact StatementRun.seqNext (fn := opDispatchFn) callRun retRun

#print axioms opAdd_dispatch_arm_run

/-- Exact price of the dispatcher arm. -/
theorem opAdd_dispatch_arm_score (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent) :
    coeff.score (executionWork (opAddDispatchArmEvents d bodyPost bodyEvents)) =
      opAddDispatchArmLocalCost coeff d bodyPost bodyEvents := by
  rfl

#print axioms opAdd_dispatch_arm_score


/-- The `op == 1` case of the dispatcher selects the `op_add` arm. -/
theorem opAdd_dispatch_ite_run (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent)
    (armRun : StatementRun opDispatchFn d (.seq (.call (some (none, none)) (ofString "op_add") [])
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddDispatchArmEvents d bodyPost bodyEvents))
    (opValue : d.locals.lookup (ofString "op") = some (.val (.word (1 : BitVec 64)))) :
    StatementRun opDispatchFn d (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
        (.const (1 : BitVec 64)))
        (.seq (.call (some (none, none)) (ofString "op_add") [])
          (.return (.const (0 : BitVec 64)))) .skip)
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (.statement :: .cost (statementUnit + branchMoves opDispatchFn) :: (expressionEvents d (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
        (.const (1 : BitVec 64))) ++ opAddDispatchArmEvents d bodyPost bodyEvents)) := by
  have guardValue : expressionValue d (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
      (.const (1 : BitVec 64))) = some (.val (.word 1)) := by
    unfold expressionValue
    simp [evalHOLExact, toExact, opValue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.lt_def]
  exact StatementRun.iteYes (fn := opDispatchFn) (costedExpression_events d _ _ guardValue) (by decide) armRun

#print axioms opAdd_dispatch_ite_run

end InitECandidate.Runtime.FineCost
