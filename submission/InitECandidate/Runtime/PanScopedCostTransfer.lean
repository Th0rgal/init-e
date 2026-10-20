import InitECandidate.Runtime.PanScalarCostModel
import InitECandidate.Runtime.LoopExecutedWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Width coverage only for the local names read by a particular expression. -/
def LocalWidthsFitOn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (variables : List MlStringHOL) : Prop :=
  ∀ name, name ∈ variables → ∀ shape names,
    context.vars.lookup name = some (shape, names) →
    names.length ≤ 1 + resultWords s (.var .local name)

private theorem scoped_layout_left {F : Type} {s : PanSemStateFiniteExact 64 F}
    {context : PanToCrepContextExact 64} {left right : List MlStringHOL}
    (layout : LocalWidthsFitOn s context (left ++ right)) : LocalWidthsFitOn s context left := by
  intro name member shape names mapped
  exact layout name (List.mem_append_left _ member) shape names mapped

private theorem scoped_layout_right {F : Type} {s : PanSemStateFiniteExact 64 F}
    {context : PanToCrepContextExact 64} {left right : List MlStringHOL}
    (layout : LocalWidthsFitOn s context (left ++ right)) : LocalWidthsFitOn s context right := by
  intro name member shape names mapped
  exact layout name (List.mem_append_right _ member) shape names mapped

private theorem scoped_expression_event_score :
    scalarLoweringWeights.score WorkEvent.expression.units = 4 := by
  simp [scalarLoweringWeights, Work.score, WorkEvent.units]

theorem scoped_scalar_lowering_cost_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) :
    ∀ e : ExpHOL 64, LocalWidthsFitOn s context (varExpHOL e) → scalarLowering e = true →
      panLoweringAllowance context e ≤ expressionCost scalarLoweringWeights s e := by
  refine ExpHOL.rec
    (motive_1 := fun e => LocalWidthsFitOn s context (varExpHOL e) → scalarLowering e = true →
      panLoweringAllowance context e ≤ expressionCost scalarLoweringWeights s e)
    (motive_2 := fun es => LocalWidthsFitOn s context ((es.map varExpHOL).flatten) → scalarLoweringList es = true →
      panLoweringListAllowance context es ≤ expressionListCost scalarLoweringWeights s es)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value layout supported
    try simp only [varExpHOL] at layout
    have entry := expressionCost_entry scalarLoweringWeights s (.const value)
    simp only [panLoweringAllowance]
    change 4 ≤ _ at entry
    omega
  · intro kind name layout supported
    try simp only [varExpHOL] at layout
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
        have fits := layout name (by simp [varExpHOL]) shape names found
        simp only [found]
        unfold expressionCost
        rw [expressionEvents]
        simp [executionWork, Work.score, Work.plus, WorkEvent.units, scalarLoweringWeights]
        omega
    | «global» =>
      have entry := expressionCost_entry scalarLoweringWeights s (.var .global name)
      change 4 ≤ _ at entry
      simp only [panLoweringAllowance]; omega
  · intro fields ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scoped_expression_event_score]
    omega
  · intro index value ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scoped_expression_event_score]
    omega
  · intro name fields ih layout supported
    try simp only [varExpHOL] at layout
    have entry := expressionCost_entry scalarLoweringWeights s (.nstruct name fields)
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro name value ih layout supported
    try simp only [varExpHOL] at layout
    have entry := expressionCost_entry scalarLoweringWeights s (.nfield name value)
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro shape address ih layout supported
    try simp only [varExpHOL] at layout
    cases shape with
    | named name => simp [scalarLowering] at supported
    | comb shapes => simp [scalarLowering] at supported
    | one =>
      have smaller := ih layout (by simpa only [scalarLowering] using supported)
      simp only [expressionCost, expressionListCost] at smaller
      simp only [panLoweringAllowance, sizeOfShapeHOL, Nat.one_mul]
      unfold expressionCost
      rw [expressionEvents]
      simp only [isWfShapeExactHOL, ↓reduceIte, executionWork_score_cons, executionWork_score_append]
      simp only [scoped_expression_event_score]
      omega
  · intro address ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scoped_expression_event_score]
    omega
  · intro address ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scoped_expression_event_score]
    omega
  · intro operator args ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scoped_expression_event_score]
    omega
  · intro operator args ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [scalarLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scoped_expression_event_score]
    omega
  · intro operator left right ihLeft ihRight layout supported
    try simp only [varExpHOL] at layout
    simp only [scalarLowering, Bool.and_eq_true] at supported
    have a := ihLeft (scoped_layout_left layout) supported.1
    have b := ihRight (scoped_layout_right layout) supported.2
    simp only [expressionCost] at a b
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scoped_expression_event_score]
    omega
  · intro operator left right ihLeft ihRight layout supported
    try simp only [varExpHOL] at layout
    simp only [scalarLowering, Bool.and_eq_true] at supported
    have a := ihLeft (scoped_layout_left layout) supported.1
    have b := ihRight (scoped_layout_right layout) supported.2
    simp only [expressionCost] at a b
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [scoped_expression_event_score]
    omega
  · intro layout supported
    try simp only [varExpHOL] at layout
    have entry := expressionCost_entry scalarLoweringWeights s .baseAddr
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro layout supported
    try simp only [varExpHOL] at layout
    have entry := expressionCost_entry scalarLoweringWeights s .topAddr
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro layout supported
    try simp only [varExpHOL] at layout
    have entry := expressionCost_entry scalarLoweringWeights s .bytesInWord
    change 4 ≤ _ at entry
    simp only [panLoweringAllowance]; omega
  · intro layout supported
    try simp only [varExpHOL] at layout
    simp [panLoweringListAllowance, expressionListCost, expressionListEvents, executionWork, Work.score]
  · intro head tail ihHead ihTail layout supported
    simp only [List.map_cons, List.flatten_cons] at layout
    simp only [scalarLoweringList, Bool.and_eq_true] at supported
    have a := ihHead (scoped_layout_left layout) supported.1
    have b := ihTail (scoped_layout_right layout) supported.2
    simp only [panLoweringListAllowance]
    unfold expressionListCost
    rw [expressionListEvents, executionWork_score_append]
    exact Nat.add_le_add a b
  · trivial
  · intros; trivial
  · intros; trivial


#print axioms scoped_scalar_lowering_cost_bound
end InitECandidate.Runtime.FineCost
