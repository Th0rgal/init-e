import InitECandidate.Runtime.PanBulkLoadCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

private theorem bulk_layout_left {F : Type} {s : PanSemStateFiniteExact 64 F}
    {context : PanToCrepContextExact 64} {left right : List MlStringHOL}
    (layout : LocalWidthsFitOn s context (left ++ right)) : LocalWidthsFitOn s context left := by
  intro name member shape names mapped
  exact layout name (List.mem_append_left _ member) shape names mapped

private theorem bulk_layout_right {F : Type} {s : PanSemStateFiniteExact 64 F}
    {context : PanToCrepContextExact 64} {left right : List MlStringHOL}
    (layout : LocalWidthsFitOn s context (left ++ right)) : LocalWidthsFitOn s context right := by
  intro name member shape names mapped
  exact layout name (List.mem_append_right _ member) shape names mapped

private theorem bulk_expression_event_score :
    scalarLoweringWeights.score WorkEvent.expression.units = 4 := by
  simp [scalarLoweringWeights, Work.score, WorkEvent.units]

mutual
  /-- Bounded multiword loads require a scalar address; thus address replay
  does not recursively multiply the work of other multiword loads. -/
  noncomputable def boundedBulkLowering {F : Type} (s : PanSemStateFiniteExact 64 F) : ExpHOL 64 → Bool
    | .load shape address => decide (sizeOfShapeHOL shape ≤ 6) &&
        (scalarLowering address && isWfShapeExactHOL s.structs shape)
    | .rstruct fields | .op _ fields | .panop _ fields => boundedBulkLoweringList s fields
    | .rfield _ value | .load32 value | .loadByte value => boundedBulkLowering s value
    | .cmp _ left right | .shift _ left right => boundedBulkLowering s left && boundedBulkLowering s right
    | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
  noncomputable def boundedBulkLoweringList {F : Type} (s : PanSemStateFiniteExact 64 F) : List (ExpHOL 64) → Bool
    | [] => true
    | head :: tail => boundedBulkLowering s head && boundedBulkLoweringList s tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem bounded_bulk_lowering_cost_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) :
    ∀ e : ExpHOL 64, LocalWidthsFitOn s context (varExpHOL e) → boundedBulkLowering s e = true →
      panLoweringAllowance context e ≤ 6 * expressionCost scalarLoweringWeights s e := by
  refine ExpHOL.rec
    (motive_1 := fun e => LocalWidthsFitOn s context (varExpHOL e) → boundedBulkLowering s e = true →
      panLoweringAllowance context e ≤ 6 * expressionCost scalarLoweringWeights s e)
    (motive_2 := fun es => LocalWidthsFitOn s context ((es.map varExpHOL).flatten) → boundedBulkLoweringList s es = true →
      panLoweringListAllowance context es ≤ 6 * expressionListCost scalarLoweringWeights s es)
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
        simpa only [found] using (show 1 ≤ 6 * expressionCost scalarLoweringWeights s (.var .local name) by omega)
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
    have smaller := ih layout (by simpa only [boundedBulkLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [bulk_expression_event_score]
    omega
  · intro index value ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [boundedBulkLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [bulk_expression_event_score]
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
    simp only [boundedBulkLowering, Bool.and_eq_true, decide_eq_true_eq] at supported
    simp only [varExpHOL] at layout
    exact bulk_load_source_allowance_bound s context shape address layout
      supported.2.1 supported.1 supported.2.2
  · intro address ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [boundedBulkLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [bulk_expression_event_score]
    omega
  · intro address ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [boundedBulkLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [bulk_expression_event_score]
    omega
  · intro operator args ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [boundedBulkLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [bulk_expression_event_score]
    omega
  · intro operator args ih layout supported
    try simp only [varExpHOL] at layout
    have smaller := ih layout (by simpa only [boundedBulkLowering] using supported)
    simp only [expressionCost, expressionListCost] at smaller
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [bulk_expression_event_score]
    omega
  · intro operator left right ihLeft ihRight layout supported
    try simp only [varExpHOL] at layout
    simp only [boundedBulkLowering, Bool.and_eq_true] at supported
    have a := ihLeft (bulk_layout_left layout) supported.1
    have b := ihRight (bulk_layout_right layout) supported.2
    simp only [expressionCost] at a b
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [bulk_expression_event_score]
    omega
  · intro operator left right ihLeft ihRight layout supported
    try simp only [varExpHOL] at layout
    simp only [boundedBulkLowering, Bool.and_eq_true] at supported
    have a := ihLeft (bulk_layout_left layout) supported.1
    have b := ihRight (bulk_layout_right layout) supported.2
    simp only [expressionCost] at a b
    simp only [panLoweringAllowance]
    unfold expressionCost
    rw [expressionEvents]
    simp only [executionWork_score_cons, executionWork_score_append]
    simp only [bulk_expression_event_score]
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
    simp only [boundedBulkLoweringList, Bool.and_eq_true] at supported
    have a := ihHead (bulk_layout_left layout) supported.1
    have b := ihTail (bulk_layout_right layout) supported.2
    simp only [expressionCost, expressionListCost] at a b
    simp only [panLoweringListAllowance]
    unfold expressionListCost
    rw [expressionListEvents, executionWork_score_append]
    omega
  · trivial
  · intros; trivial
  · intros; trivial


#print axioms bounded_bulk_lowering_cost_bound
end InitECandidate.Runtime.FineCost
