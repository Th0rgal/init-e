import InitECandidate.Runtime.GuestCostOpAddDispatch
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- The `op == 0` guard skip trace. -/
noncomputable def opAddOuterZeroEvents (d : PanSemStateFiniteExact 64 Guest.HostMemory) :
    List WorkEvent :=
  .statement :: (expressionEvents d (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
    (.const (0 : BitVec 64))) ++ [.statement])

/-- The `op == 1` guard and `op_add` arm trace. -/
noncomputable def opAddOuterOneEvents (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent) :
    List WorkEvent :=
  .statement :: (expressionEvents d (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
    (.const (1 : BitVec 64))) ++ opAddDispatchArmEvents d bodyPost bodyEvents)

/-- The `op < 16` guard and its selected zero/one guards and arm. -/
noncomputable def opAddOuterSixteenEvents (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent) :
    List WorkEvent :=
  .statement :: (expressionEvents d (.cmp Cmp.lower (.var VarKind.local (ofString "op"))
    (.const (16 : BitVec 64))) ++ (opAddOuterZeroEvents d ++ opAddOuterOneEvents d bodyPost bodyEvents))

/-- The full outer dispatcher guard trace for `op = 1`. -/
noncomputable def opAddOuterThirtyTwoEvents (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent) :
    List WorkEvent :=
  .statement :: (expressionEvents d (.cmp Cmp.lower (.var VarKind.local (ofString "op"))
    (.const (32 : BitVec 64))) ++ opAddOuterSixteenEvents d bodyPost bodyEvents)


/-- The dispatcher's `op == 0` guard, proven false at `op = 1`. -/
theorem opAddOuter_opZero_iteNo (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rest : ProgHOL 64)
    (opValue : d.locals.lookup (ofString "op") = some (.val (.word (1 : BitVec 64)))) :
    StatementRun d
      (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (0 : BitVec 64)))
        (.seq (.call (some (none, none)) (ofString "op_stop") [])
          (.return (.const (0 : BitVec 64)))) .skip)
      none d
      (opAddOuterZeroEvents d) := by
  have guardValue : expressionValue d (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
      (.const (0 : BitVec 64))) = some (.val (.word 0)) := by
    unfold expressionValue
    simp [evalHOLExact, toExact, opValue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simpa [opAddOuterZeroEvents] using StatementRun.iteNo (r := none) (post := d) (bodyEvents := [.statement])
    (costedExpression_events d _ _ guardValue) (StatementRun.skip d)

#print axioms opAddOuter_opZero_iteNo

/-- The `op == 0` skip followed by the terminating `op == 1` arm: the arm's
termination lets the surrounding `seq` stop without evaluating later arms. -/
theorem opAddOuter_opZero_opOne_run (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent)
    (rest : ProgHOL 64)
    (armRun : StatementRun d (.seq (.call (some (none, none)) (ofString "op_add") [])
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddDispatchArmEvents d bodyPost bodyEvents))
    (opValue : d.locals.lookup (ofString "op") = some (.val (.word (1 : BitVec 64)))) :
    StatementRun d
      (.seq (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (0 : BitVec 64)))
          (.seq (.call (some (none, none)) (ofString "op_stop") [])
            (.return (.const (0 : BitVec 64)))) .skip)
        (.seq (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (1 : BitVec 64)))
            (.seq (.call (some (none, none)) (ofString "op_add") [])
              (.return (.const (0 : BitVec 64)))) .skip) rest))
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddOuterZeroEvents d ++ opAddOuterOneEvents d bodyPost bodyEvents) := by
  have zero := opAddOuter_opZero_iteNo d rest opValue
  have one := opAdd_dispatch_ite_run d bodyPost bodyEvents armRun opValue
  have tail := StatementRun.seqStop (s := d) (first :=
      (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (1 : BitVec 64)))
        (.seq (.call (some (none, none)) (ofString "op_add") [])
          (.return (.const (0 : BitVec 64)))) .skip))
      (second := rest) (r := some (.returned (.val (.word 0))))
      (post := opAddDispatchArmPost d bodyPost) (by decide) one
  simpa [opAddOuterZeroEvents, opAddOuterOneEvents, opAddDispatchArmEvents] using StatementRun.seqNext zero tail

#print axioms opAddOuter_opZero_opOne_run

/-- The dispatcher's `op < 16` branch selects the terminating `op == 1` arm. -/
theorem opAddOuter_lt16_run (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent)
    (rest rest2 : ProgHOL 64)
    (armRun : StatementRun d (.seq (.call (some (none, none)) (ofString "op_add") [])
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddDispatchArmEvents d bodyPost bodyEvents))
    (opValue : d.locals.lookup (ofString "op") = some (.val (.word (1 : BitVec 64)))) :
    StatementRun d
      (.ite (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (16 : BitVec 64)))
        (.seq (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (0 : BitVec 64)))
            (.seq (.call (some (none, none)) (ofString "op_stop") [])
              (.return (.const (0 : BitVec 64)))) .skip)
          (.seq (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (1 : BitVec 64)))
              (.seq (.call (some (none, none)) (ofString "op_add") [])
                (.return (.const (0 : BitVec 64)))) .skip) rest)) rest2)
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddOuterSixteenEvents d bodyPost bodyEvents) := by
  have guardValue : expressionValue d (.cmp Cmp.lower (.var VarKind.local (ofString "op"))
      (.const (16 : BitVec 64))) = some (.val (.word 1)) := by
    unfold expressionValue
    simp [evalHOLExact, toExact, opValue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have inner := opAddOuter_opZero_opOne_run coeff d bodyPost bodyEvents rest armRun opValue
  simpa [opAddOuterZeroEvents, opAddOuterOneEvents, opAddOuterSixteenEvents, opAddDispatchArmEvents] using StatementRun.iteYes (costedExpression_events d _ _ guardValue) (by decide) inner

#print axioms opAddOuter_lt16_run

/-- The dispatcher's `op < 32` branch selects the terminating `op < 16` branch,
so the whole dispatcher body stops once the `op_add` arm returns. -/
theorem opAddOuter_lt32_run (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent)
    (rest rest2 rest2b rest3 : ProgHOL 64)
    (armRun : StatementRun d (.seq (.call (some (none, none)) (ofString "op_add") [])
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddDispatchArmEvents d bodyPost bodyEvents))
    (opValue : d.locals.lookup (ofString "op") = some (.val (.word (1 : BitVec 64)))) :
    StatementRun d
      (.seq
        (.ite (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (32 : BitVec 64)))
          (.seq
            (.ite (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (16 : BitVec 64)))
              (.seq
                (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (0 : BitVec 64)))
                  (.seq (.call (some (none, none)) (ofString "op_stop") [])
                    (.return (.const (0 : BitVec 64))))
                  .skip)
                (.seq
                  (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
                      (.const (1 : BitVec 64)))
                    (.seq (.call (some (none, none)) (ofString "op_add") [])
                      (.return (.const (0 : BitVec 64))))
                    .skip)
                  rest))
              rest2)
            rest2b)
          (.seq (.call (some (none, none)) (ofString "op_stop") [])
            (.return (.const (0 : BitVec 64)))))
        rest3)
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddOuterThirtyTwoEvents d bodyPost bodyEvents) := by
  have guardValue : expressionValue d (.cmp Cmp.lower (.var VarKind.local (ofString "op"))
      (.const (32 : BitVec 64))) = some (.val (.word 1)) := by
    unfold expressionValue
    simp [evalHOLExact, toExact, opValue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have inner := opAddOuter_lt16_run coeff d bodyPost bodyEvents rest rest2 armRun opValue
  have branch := StatementRun.seqStop (s := d)
      (first :=
        (.ite (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (16 : BitVec 64)))
          (.seq
            (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (0 : BitVec 64)))
              (.seq (.call (some (none, none)) (ofString "op_stop") [])
                (.return (.const (0 : BitVec 64))))
              .skip)
            (.seq
              (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (1 : BitVec 64)))
                (.seq (.call (some (none, none)) (ofString "op_add") [])
                  (.return (.const (0 : BitVec 64))))
                .skip)
              rest))
          rest2))
      (second := rest2b) (r := some (.returned (.val (.word 0))))
      (post := opAddDispatchArmPost d bodyPost) (by decide) inner
  have iteRun := StatementRun.iteYes
    (no := (.seq (.call (some (none, none)) (ofString "op_stop") [])
      (.return (.const (0 : BitVec 64)))))
    (costedExpression_events d _ _ guardValue) (by decide) branch
  have whole := StatementRun.seqStop (s := d)
      (first :=
        (.ite (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (32 : BitVec 64)))
          (.seq
            (.ite (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (16 : BitVec 64)))
              (.seq
                (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (0 : BitVec 64)))
                  (.seq (.call (some (none, none)) (ofString "op_stop") [])
                    (.return (.const (0 : BitVec 64))))
                  .skip)
                (.seq
                  (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
                      (.const (1 : BitVec 64)))
                    (.seq (.call (some (none, none)) (ofString "op_add") [])
                      (.return (.const (0 : BitVec 64))))
                    .skip)
                  rest))
              rest2)
            rest2b)
          (.seq (.call (some (none, none)) (ofString "op_stop") [])
            (.return (.const (0 : BitVec 64))))))
      (second := rest3) (r := some (.returned (.val (.word 0))))
      (post := opAddDispatchArmPost d bodyPost) (by decide) iteRun
  simpa [opAddOuterZeroEvents, opAddOuterOneEvents, opAddOuterSixteenEvents, opAddOuterThirtyTwoEvents, opAddDispatchArmEvents] using whole

#print axioms opAddOuter_lt32_run


/-- Price of one dispatcher guard statement and its condition. -/
noncomputable def opAddOuterGuardCost (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory) (condition : ExpHOL 64) : Nat :=
  coeff.score (executionWork (.statement :: expressionEvents d condition))

/-- The outer guard trace splits into the `op < 32` guard and the inner trace. -/
theorem opAddOuterThirtyTwoEvents_score (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent) :
    coeff.score (executionWork (opAddOuterThirtyTwoEvents d bodyPost bodyEvents)) =
      opAddOuterGuardCost coeff d
        (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (32 : BitVec 64))) +
      coeff.score (executionWork (opAddOuterSixteenEvents d bodyPost bodyEvents)) := by
  unfold opAddOuterThirtyTwoEvents opAddOuterGuardCost
  simp [executionWork_score_append, executionWork_score_cons]
  omega

#print axioms opAddOuterThirtyTwoEvents_score

/-- The full outer guard price is the two lower guards, the zero guard skip, and
the `op == 1` arm price. -/
theorem opAddOuterThirtyTwoEvents_localCost (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent) :
    coeff.score (executionWork (opAddOuterThirtyTwoEvents d bodyPost bodyEvents)) =
      opAddOuterGuardCost coeff d
        (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (32 : BitVec 64))) +
      opAddOuterGuardCost coeff d
        (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (16 : BitVec 64))) +
      coeff.score (executionWork (opAddOuterZeroEvents d)) +
      coeff.score (executionWork (opAddOuterOneEvents d bodyPost bodyEvents)) := by
  unfold opAddOuterThirtyTwoEvents opAddOuterSixteenEvents opAddOuterGuardCost
  simp [executionWork_score_append, executionWork_score_cons]
  omega

#print axioms opAddOuterThirtyTwoEvents_localCost


/-- Dispatcher-body corollary: once the actual `op_dispatch` body is presented in
the canonical guard nesting, the `op = 1` run follows without evaluating any
later opcode arm. The body-shape premise is discharged by `rfl` at the call site. -/
theorem opAddOuter_dispatch_body_run (coeff : Work)
    (d : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory) (bodyEvents : List WorkEvent)
    (rest rest2 rest2b rest3 : ProgHOL 64)
    (armRun : StatementRun (callEntryStateHOLFinite d HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_op_add) (some (.returned (.val (.word 0))))
      bodyPost bodyEvents)
    (dFrame : d.globals.lookup (ofString "ev") = some (.val (.word 0)))
    (dClock : d.clock ≠ 0)
    (dInstalled : d.code.lookup = originalRuntimeCode.lookup)
    (opValue : d.locals.lookup (ofString "op") = some (.val (.word (1 : BitVec 64))))
    (hbody : sourceFunctionBody Guest.guestFn_op_dispatch =
      (.seq
        (.ite (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (32 : BitVec 64)))
          (.seq
            (.ite (.cmp Cmp.lower (.var VarKind.local (ofString "op")) (.const (16 : BitVec 64)))
              (.seq
                (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op")) (.const (0 : BitVec 64)))
                  (.seq (.call (some (none, none)) (ofString "op_stop") [])
                    (.return (.const (0 : BitVec 64))))
                  .skip)
                (.seq
                  (.ite (.cmp Cmp.equal (.var VarKind.local (ofString "op"))
                      (.const (1 : BitVec 64)))
                    (.seq (.call (some (none, none)) (ofString "op_add") [])
                      (.return (.const (0 : BitVec 64))))
                    .skip)
                  rest))
              rest2)
            rest2b)
          (.seq (.call (some (none, none)) (ofString "op_stop") [])
            (.return (.const (0 : BitVec 64)))))
        rest3)) :
    StatementRun d (sourceFunctionBody Guest.guestFn_op_dispatch)
      (some (.returned (.val (.word 0)))) (opAddDispatchArmPost d bodyPost)
      (opAddOuterThirtyTwoEvents d bodyPost bodyEvents) := by
  have arm := opAdd_dispatch_arm_run coeff d bodyPost bodyEvents armRun dFrame dClock dInstalled
  have run := opAddOuter_lt32_run coeff d bodyPost bodyEvents rest rest2 rest2b rest3 arm opValue
  rw [hbody]
  simpa [opAddOuterThirtyTwoEvents] using run

#print axioms opAddOuter_dispatch_body_run
end InitECandidate.Runtime.FineCost
