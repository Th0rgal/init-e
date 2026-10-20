import InitECandidate.Runtime.PanLayoutCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Up to six flattened words can replay a scalar address at most six times.
The four-unit source entry charge also covers the fixed per-word offset nodes. -/
theorem bulk_load_source_allowance_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (shape : ShapeHOL) (address : ExpHOL 64)
    (layout : LocalWidthsFitOn s context (varExpHOL address))
    (supported : scalarLowering address = true)
    (width : sizeOfShapeHOL shape ≤ 6)
    (wellFormed : isWfShapeExactHOL s.structs shape = true) :
    panLoweringAllowance context (.load shape address) ≤
      6 * expressionCost scalarLoweringWeights s (.load shape address) := by
  have addressBound := scoped_scalar_lowering_cost_bound s context address layout supported
  have replay := Nat.mul_le_mul width (Nat.add_le_add_right addressBound 3)
  simp only [panLoweringAllowance]
  unfold expressionCost
  rw [expressionEvents]
  simp only [wellFormed, ↓reduceIte, executionWork_score_cons, executionWork_score_append]
  have entry : scalarLoweringWeights.score WorkEvent.expression.units = 4 := by
    simp [scalarLoweringWeights, Work.score, WorkEvent.units]
  rw [entry]
  simp only [expressionCost] at replay
  omega

/-- Successful loads obtain their address layout from the existing compiler
locals relation. No independent context coverage or read-presence assumption. -/
theorem successful_bulk_load_source_to_loop_cost {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (shape : ShapeHOL) (address : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : expressionValue s (.load shape address) = some value)
    (supported : scalarLowering address = true) (width : sizeOfShapeHOL shape ≤ 6)
    (loopContext : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (state : LoopSemStateFiniteExact 64 G) :
    let expressions := (compileExpExactHOLW context (.load shape address)).1
    let compiled := compileExpsHOLExact loopContext tmp live expressions
    ∃ cost, LoopWorkRun state (loopNestedSeqHOL compiled.1)
        (LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL compiled.1) state) cost ∧
      cost + loopValuesWork compiled.2.1 + compiled.2.1.length ≤
        36 * expressionCost scalarLoweringWeights s (.load shape address) := by
  have present := expression_success_locals_present s (.load shape address) value evaluated
  simp only [varExpHOL] at present
  have layout := scopedWidthsFit_of_related_present s context targetLocals related address present
  have wellFormed : isWfShapeExactHOL s.structs shape = true := by
    cases wf : isWfShapeExactHOL s.structs shape with
    | true => rfl
    | false => simp [expressionValue, evalHOLExact, wf] at evaluated
  have sourceBound := bulk_load_source_allowance_bound s context shape address layout supported width wellFormed
  obtain ⟨cost, trace, bound⟩ := compiled_pan_expression_trace context loopContext tmp live
    (.load shape address) state
  refine ⟨cost, trace, Nat.le_trans bound ?_⟩
  simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 6 sourceBound

#print axioms bulk_load_source_allowance_bound
#print axioms successful_bulk_load_source_to_loop_cost
end InitECandidate.Runtime.FineCost
