import InitECandidate.Runtime.GuestBulkLoadSites
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

private theorem shape_wf_empty_mono (context : StructContextExact) :
    ∀ shape : ShapeHOL, isWfShapeExactHOL ([] : StructContextExact) shape = true →
      isWfShapeExactHOL context shape = true := by
  refine ShapeHOL.rec
    (motive_1 := fun shape => isWfShapeExactHOL ([] : StructContextExact) shape = true →
      isWfShapeExactHOL context shape = true)
    (motive_2 := fun shapes => isWfShapesExactHOL ([] : StructContextExact) shapes = true →
      isWfShapesExactHOL context shapes = true) ?_ ?_ ?_ ?_ ?_
  · intro h; rfl
  · intro shapes ih; exact ih
  · intro name h; simp [isWfShapeExactHOL, structContextLookupHOL] at h
  · intro h; rfl
  · intro head tail ihHead ihTail h
    simp only [isWfShapesExactHOL, Bool.and_eq_true] at h ⊢
    exact ⟨ihHead h.1, ihTail h.2⟩

/-- A checked load-site predicate implies the state-dependent support condition
of the cost theorem in every source structure context. -/
theorem bulk_sites_imply_supported {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ e : ExpHOL 64, bulkLoadSitesExp e = true → boundedBulkLowering s e = true := by
  refine ExpHOL.rec
    (motive_1 := fun e => bulkLoadSitesExp e = true → boundedBulkLowering s e = true)
    (motive_2 := fun es => bulkLoadSitesExps es = true → boundedBulkLoweringList s es = true)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intros; simp [boundedBulkLowering, boundedBulkLoweringList]
  · intros; simp [boundedBulkLowering, boundedBulkLoweringList]
  · intro fields ih; simpa only [bulkLoadSitesExp, boundedBulkLowering] using ih
  · intro index value ih; simpa only [bulkLoadSitesExp, boundedBulkLowering] using ih
  · intros; simp [boundedBulkLowering, boundedBulkLoweringList]
  · intros; simp [boundedBulkLowering, boundedBulkLoweringList]
  · intro shape address ih h
    simp only [bulkLoadSitesExp, Bool.and_eq_true] at h
    simp only [boundedBulkLowering, Bool.and_eq_true]
    exact ⟨h.1.1.1, h.1.1.2, shape_wf_empty_mono s.structs shape h.1.2⟩
  · intro address ih; simpa only [bulkLoadSitesExp, boundedBulkLowering] using ih
  · intro address ih; simpa only [bulkLoadSitesExp, boundedBulkLowering] using ih
  · intro operator args ih; simpa only [bulkLoadSitesExp, boundedBulkLowering] using ih
  · intro operator args ih; simpa only [bulkLoadSitesExp, boundedBulkLowering] using ih
  · intro operator left right ihLeft ihRight h
    simp only [bulkLoadSitesExp, Bool.and_eq_true] at h
    simp only [boundedBulkLowering, Bool.and_eq_true]
    exact ⟨ihLeft h.1, ihRight h.2⟩
  · intro operator left right ihLeft ihRight h
    simp only [bulkLoadSitesExp, Bool.and_eq_true] at h
    simp only [boundedBulkLowering, Bool.and_eq_true]
    exact ⟨ihLeft h.1, ihRight h.2⟩
  · intros; simp [boundedBulkLowering, boundedBulkLoweringList]
  · intros; simp [boundedBulkLowering, boundedBulkLoweringList]
  · intros; simp [boundedBulkLowering, boundedBulkLoweringList]
  · intros; simp [boundedBulkLowering, boundedBulkLoweringList]
  · intro head tail ihHead ihTail h
    simp only [bulkLoadSitesExps, Bool.and_eq_true] at h
    simp only [boundedBulkLoweringList, Bool.and_eq_true]
    exact ⟨ihHead h.1, ihTail h.2⟩
  · trivial
  · intros; trivial
  · intros; trivial

/-- Checked load sites plus successful evaluation suffice for the compound
source-expression to executed Loop-work bound, with no independent layout widths. -/
theorem checked_bulk_source_to_loop_cost {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (expression : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : expressionValue s expression = some value)
    (checked : bulkLoadSitesExp expression = true)
    (loopContext : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (state : LoopSemStateFiniteExact 64 G) :
    let expressions := (compileExpExactHOLW context expression).1
    let compiled := compileExpsHOLExact loopContext tmp live expressions
    ∃ cost, LoopWorkRun state (loopNestedSeqHOL compiled.1)
        (LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL compiled.1) state) cost ∧
      cost + loopNativeValues compiled.2.1 + 39 * compiled.2.1.length ≤
        960 * expressionCost scalarLoweringWeights s expression := by
  have present := expression_success_locals_present s expression value evaluated
  have layout := scopedWidthsFit_of_related_present s context targetLocals related expression present
  have supported := bulk_sites_imply_supported s expression checked
  have sourceBound := bounded_bulk_lowering_cost_bound s context expression layout supported
  obtain ⟨cost, trace, bound⟩ := compiled_pan_expression_trace context loopContext tmp live expression state
  refine ⟨cost, trace, Nat.le_trans bound ?_⟩
  simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 160 sourceBound

#print axioms checked_bulk_source_to_loop_cost

#print axioms bulk_sites_imply_supported
end InitECandidate.Runtime.FineCost
