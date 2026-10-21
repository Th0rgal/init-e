import InitECandidate.Runtime.GuestCostChargeFamily
import InitECandidate.Runtime.GasFrameExpressions
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace InitECandidate.Runtime.FineCost

variable {fn : MlS}

theorem pcAdd_score_cost (coeff : Work) (n : Nat) :
    coeff.score (WorkEvent.cost n).units = coeff.nativeCost * n := by
  simp [Work.score, WorkEvent.units]
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

/-- Address `ev[0]`: the program counter cell of the current frame. -/
def pcAddAddress : ExpHOL 64 := fundingAddress (0 : BitVec 64)

/-- The word stored into `ev[0]`: the fetched program counter plus the local `n`. -/
noncomputable def pcAddValue : ExpHOL 64 :=
  .op .add [fundingLoad (0 : BitVec 64), .var VarKind.local (ofString "n")]

/-- The compiled body of the `pc_add` helper. -/
noncomputable def pcAddBody : ProgHOL 64 :=
  .seq (.store pcAddAddress pcAddValue) (.return (.const 0))

/-- The pinned installed AST of the `pc_add` helper. -/
theorem source_pcAdd_body : sourceFunctionBody Guest.guestFn_pc_add = pcAddBody := by
  cbv

/-- The address expression evaluates to the program counter cell address. -/
theorem eval_pcAddAddress (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame))) :
    expressionValue s pcAddAddress = some (.val (.word (frame + 0))) := by
  classical
  unfold expressionValue pcAddAddress fundingAddress
  simp [evalHOLExact, evalListHOLExact, toExact, hFrame, wordOpHOL, wordOp, valueIsWord,
    valueWord]

/-- The stored word is the fetched program counter plus `n`, evaluated from the
actual cell, its domain membership and the actual local. -/
theorem eval_pcAddValue (s : PanSemStateFiniteExact 64 F) (frame value n : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hN : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (domain : s.memaddrs (frame + 0)) (memory : s.memory (frame + 0) = .word value) :
    @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) pcAddValue =
      some (.val (.word (value + n))) := by
  classical
  unfold pcAddValue
  simp only [evalHOLExact, evalListHOLExact]
  rw [eval_fundingLoad s frame 0 value hFrame domain memory]
  simp [evalHOLExact, toExact, hN, valueIsWord, valueWord, wordOpHOL, wordOp]

/-- The program-counter store of the helper. -/
theorem pcAdd_store_run (s : PanSemStateFiniteExact 64 F) (frame value n : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hN : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (domain : s.memaddrs (frame + 0)) (memory : s.memory (frame + 0) = .word value) :
    StatementRun fn s (.store pcAddAddress pcAddValue) none
      { s with memory := writeWordMemory s (frame + 0) (value + n) }
      (.statement :: (expressionEvents s pcAddAddress ++
        expressionEvents s pcAddValue ++
        [.memory (flattenHOL (.val (.word (value + n)))).length, .cost (storeOverhead (flattenHOL (.val (.word (value + n)))).length)])) := by
  classical
  have dst : CostedExpressionRun s pcAddAddress (some (.val (.word (frame + 0))))
      (expressionEvents s pcAddAddress) :=
    costedExpression_events s _ _ (eval_pcAddAddress s frame hFrame)
  have src : CostedExpressionRun s pcAddValue (some (.val (.word (value + n))))
      (expressionEvents s pcAddValue) :=
    costedExpression_events s _ _ (eval_pcAddValue s frame value n hFrame hN domain memory)
  have write : @panMemStoresHOL 64 _ (frame + 0)
      (flattenHOL (.val (.word (value + n)))) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory =
      some (writeWordMemory s (frame + 0) (value + n)) := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
    rw [if_pos domain]
    rfl
  exact StatementRun.storeValue (destination := pcAddAddress) (source := pcAddValue)
    dst src write

/-- The final `return 0` of the helper. -/
theorem pcAdd_return_run (s : PanSemStateFiniteExact 64 F) :
    StatementRun fn s (.return (.const 0)) (some (.returned (.val (.word 0))))
      (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const 0) ++
        [.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length + returnMoves fn)])) :=
  StatementRun.returnValue (expression := .const (0 : BitVec 64))
    (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
    (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])

/-- Recorded work of one complete `pc_add` helper run. -/
noncomputable def pcAddEvents (s : PanSemStateFiniteExact 64 F) (frame value n : BitVec 64) :
    List WorkEvent :=
  let stored : PanSemStateFiniteExact 64 F :=
    { s with memory := writeWordMemory s (frame + 0) (value + n) }
  .statement ::
    (expressionEvents s pcAddAddress ++ expressionEvents s pcAddValue ++
      [.memory (flattenHOL (.val (.word (value + n)))).length, .cost (storeOverhead (flattenHOL (.val (.word (value + n)))).length)] ++
      (.statement :: (expressionEvents stored (.const 0) ++
        [.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length + returnMoves fn)])))

/-- The actual installed `pc_add` helper runs on the fetched program counter. -/
theorem pcAdd_run (s : PanSemStateFiniteExact 64 F) (frame value n : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hN : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (domain : s.memaddrs (frame + 0)) (memory : s.memory (frame + 0) = .word value) :
    StatementRun fn s (sourceFunctionBody Guest.guestFn_pc_add)
      (some (.returned (.val (.word 0))))
      (emptyLocalsHOLFinite { s with memory := writeWordMemory s (frame + 0) (value + n) })
      (pcAddEvents (fn := fn) s frame value n) := by
  classical
  rw [source_pcAdd_body]
  unfold pcAddBody pcAddEvents
  exact StatementRun.seqNext (fn := fn) (pcAdd_store_run (fn := fn) s frame value n hFrame hN domain memory)
    (pcAdd_return_run (fn := fn) { s with memory := writeWordMemory s (frame + 0) (value + n) })

/-- Explicit coefficient price of one `pc_add` helper run. -/
theorem pcAddEvents_score (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (frame value n : BitVec 64) :
    coeff.score (executionWork (pcAddEvents (fn := fn) s frame value n)) ≤
      16 * coeff.statements +
        expressionCost coeff s pcAddAddress +
        expressionCost coeff s pcAddValue +
        coeff.memoryAccesses * (flattenHOL (.val (.word (value + n)))).length +
        coeff.nativeCost * storeOverhead (flattenHOL (.val (.word (value + n)))).length +
        expressionCost coeff { s with memory := writeWordMemory s (frame + 0) (value + n) }
          (.const 0) +
        coeff.movedWords * (flattenHOL (.val (.word (0 : BitVec 64)))).length +
        coeff.score (WorkEvent.cost (returnOverhead (flattenHOL (.val (.word (0 : BitVec 64)))).length + returnMoves fn)).units := by
  unfold pcAddEvents expressionCost
  simp only [executionWork_score_cons, executionWork_score_append, score_statement,
    guest_score_copy, score_frame, guest_score_memory, score_singleton, score_expression,
    executionWork_nil_score, List.append_nil, pcAdd_score_cost]
  omega

#print axioms source_pcAdd_body
#print axioms eval_pcAddAddress
#print axioms eval_pcAddValue
#print axioms pcAdd_store_run
#print axioms pcAdd_run
#print axioms pcAddEvents_score
end InitECandidate.Runtime.FineCost
