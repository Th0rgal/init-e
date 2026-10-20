import InitECandidate.Runtime.PanTotalExpressionCost
import InitECandidate.Runtime.PanLoweringAllowance
import InitECandidate.Runtime.LoopExecutedWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Local source units sufficient for scalar expression flattening. This is
not the final native coefficient vector. -/
def scalarLoweringWeights : Work := { expressions := 4, movedWords := 1 }

mutual
  def scalarLowering : ExpHOL 64 → Bool
    | .load .one address => scalarLowering address
    | .load _ _ => false
    | .rstruct fields | .op _ fields | .panop _ fields => scalarLoweringList fields
    | .rfield _ value | .load32 value | .loadByte value => scalarLowering value
    | .cmp _ left right | .shift _ left right => scalarLowering left && scalarLowering right
    | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
  def scalarLoweringList : List (ExpHOL 64) → Bool
    | [] => true
    | head :: tail => scalarLowering head && scalarLoweringList tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

noncomputable def expressionListCost {F : Type} (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (es : List (ExpHOL 64)) : Nat := coeff.score (executionWork (expressionListEvents s es))

def LocalWidthsFit {F : Type} (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64) : Prop :=
  ∀ name shape names, context.vars.lookup name = some (shape, names) →
    names.length ≤ 1 + resultWords s (.var .local name)

private theorem scalar_expression_event_score :
    scalarLoweringWeights.score WorkEvent.expression.units = 4 := by
  simp [scalarLoweringWeights, Work.score, WorkEvent.units]

theorem scalar_lowering_cost_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (layout : LocalWidthsFit s context) :
    ∀ e : ExpHOL 64, scalarLowering e = true →
      panLoweringAllowance context e ≤ expressionCost scalarLoweringWeights s e := by
  refine ExpHOL.rec
    (motive_1 := fun e => scalarLowering e = true →
      panLoweringAllowance context e ≤ expressionCost scalarLoweringWeights s e)
    (motive_2 := fun es => scalarLoweringList es = true →
      panLoweringListAllowance context es ≤ expressionListCost scalarLoweringWeights s es)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value supported
    have entry := expressionCost_entry scalarLoweringWeights s (.const value)
    simp only [panLoweringAllowance]
    change 4 ≤ _ at entry
    omega
  · intro kind name supported
    cases kind with
    | «local» =>
      simp only [panLoweringAllowance]
      cases found : context.vars.lookup name with
      | none =>
        have entry := expressionCost_entry scalarLoweringWeights s (.var .local name)
        change 4 ≤ _ at entry
        simpa only [found] using (show 1 ≤ expressionCost scalarLoweringWeights s (.var .local name) by omega)
      | some data =>
        obtain ⟨shape, names⟩ := data
        have fits := layout name shape names found
        simp only [found]
        unfold expressionCost
        rw [expressionEvents]
        simp [executionWork, Work.score, Work.plus, WorkEvent.units, scalarLoweringWeights]
        omega
    | «global» =>
      have entry := expressionCost_entry scalarLoweringWeights s (.var .global name)
      change 4 ≤ _ at entry
      simp only [panLoweringAllowance]; omega
  · intro fields ih supported
    have smaller := ih (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scalar_expression_event_score]
    omega
  · intro index value ih supported
    have smaller := ih (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scalar_expression_event_score]
    omega
  · intro name fields ih supported
    have entry := expressionCost_entry scalarLoweringWeights s (.nstruct name fields)
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro name value ih supported
    have entry := expressionCost_entry scalarLoweringWeights s (.nfield name value)
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro shape address ih supported
    cases shape with
    | named name => simp [scalarLowering] at supported
    | comb shapes => simp [scalarLowering] at supported
    | one =>
      have smaller := ih (by simpa only [scalarLowering] using supported)
      simp only [expressionCost, expressionListCost] at smaller
      simp only [panLoweringAllowance, sizeOfShapeHOL, Nat.one_mul]
      unfold expressionCost
      rw [expressionEvents]
      simp only [isWfShapeExactHOL, ↓reduceIte, executionWork_score_cons, executionWork_score_append]
      simp only [scalar_expression_event_score]
      omega
  · intro address ih supported
    have smaller := ih (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scalar_expression_event_score]
    omega
  · intro address ih supported
    have smaller := ih (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scalar_expression_event_score]
    omega
  · intro operator args ih supported
    have smaller := ih (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scalar_expression_event_score]
    omega
  · intro operator args ih supported
    have smaller := ih (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scalar_expression_event_score]
    omega
  · intro operator left right ihLeft ihRight supported
    simp only [scalarLowering, Bool.and_eq_true] at supported
    have a := ihLeft supported.1
    have b := ihRight supported.2
    simp only [expressionCost] at a b
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scalar_expression_event_score]
    omega
  · intro operator left right ihLeft ihRight supported
    simp only [scalarLowering, Bool.and_eq_true] at supported
    have a := ihLeft supported.1
    have b := ihRight supported.2
    simp only [expressionCost] at a b
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scalar_expression_event_score]
    omega
  · intro supported
    have entry := expressionCost_entry scalarLoweringWeights s .baseAddr
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro supported
    have entry := expressionCost_entry scalarLoweringWeights s .topAddr
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro supported
    have entry := expressionCost_entry scalarLoweringWeights s .bytesInWord
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro supported
    simp [panLoweringListAllowance, expressionListCost, expressionListEvents, executionWork, Work.score]
  · intro head tail ihHead ihTail supported
    simp only [scalarLoweringList, Bool.and_eq_true] at supported
    have a := ihHead supported.1
    have b := ihTail supported.2
    simp only [panLoweringListAllowance]
    unfold expressionListCost
    rw [expressionListEvents, executionWork_score_append]
    exact Nat.add_le_add a b
  · trivial
  · intros; trivial
  · intros; trivial

/-- Executed Loop expression-code work is bounded directly by source expression
cost, with coefficient six. Variable layout is explicit; multiword loads and
the preprocessing/later backend passes require their own transfer proofs. -/
theorem scalar_source_to_loop_cost {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (panContext : PanToCrepContextExact 64)
    (loopContext : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (expression : ExpHOL 64) (state : LoopSemStateFiniteExact 64 G)
    (layout : LocalWidthsFit s panContext) (supported : scalarLowering expression = true) :
    let expressions := (compileExpExactHOLW panContext expression).1
    let compiled := compileExpsHOLExact loopContext tmp live expressions
    ∃ cost, LoopWorkRun state (loopNestedSeqHOL compiled.1)
        (LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL compiled.1) state) cost ∧
      cost + loopValuesWork compiled.2.1 + compiled.2.1.length ≤
        6 * expressionCost scalarLoweringWeights s expression := by
  obtain ⟨cost, trace, bound⟩ := compiled_pan_expression_trace
    panContext loopContext tmp live expression state
  exact ⟨cost, trace, Nat.le_trans bound (Nat.mul_le_mul_left 6
    (scalar_lowering_cost_bound s panContext layout expression supported))⟩

#print axioms scalar_source_to_loop_cost

#print axioms scalar_lowering_cost_bound
end InitECandidate.Runtime.FineCost
