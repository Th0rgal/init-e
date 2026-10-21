import InitECandidate.Runtime.SourceCostGlobalsExpr
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem globals_global_value {F : Type} {s : PanSemStateFiniteExact 64 F} {name} {value : ValueHOL 64}
    (h : expressionValue s (.var .global name) = some value) : s.globals.lookup name = some value := by
  simpa [expressionValue, evalHOLExact] using h

theorem globals_list_ok {F : Type} {s : PanSemStateFiniteExact 64 F} {head : ExpHOL 64}
    {tail : List (ExpHOL 64)}
    (ok : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (head :: tail) ≠ none) :
    expressionValue s head ≠ none ∧ @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) tail ≠ none := by
  simp only [evalListHOLExact] at ok
  constructor
  · intro h; apply ok; simp only [expressionValue] at h; simp [h]
  · intro h; apply ok; simp [h]

theorem globals_locals_eq {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t) :
    s.locals = t.locals := by
  unfold panGlobalsStateRelHOLExact at rel
  exact rel.2.1 rfl

/-- `pan_globals` preserves native expression prices: a global read is priced
by its `TopAddr`-relative load, which is exactly what `pan_globals` emits. -/
theorem globals_exprPrices_eq {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t) :
    ∀ e : ExpHOL 64, globalsReadyExp e = true → expressionValue s e ≠ none →
      exprPrices (valueInfo s.locals) (valueInfo t.globals) (compileExpExactHOL context e) =
        exprPrices (valueInfo s.locals) (valueInfo s.globals) e := by
  refine ExpHOL.rec
    (motive_1 := fun e => globalsReadyExp e = true → expressionValue s e ≠ none →
      exprPrices (valueInfo s.locals) (valueInfo t.globals) (compileExpExactHOL context e) =
        exprPrices (valueInfo s.locals) (valueInfo s.globals) e)
    (motive_2 := fun es => globalsReadyExps es = true →
      @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es ≠ none →
      exprListPrices (valueInfo s.locals) (valueInfo t.globals) (compileExpExactHOLList context es) =
        exprListPrices (valueInfo s.locals) (valueInfo s.globals) es)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value _ _
    simp [compileExpExactHOL, exprPrices]
  · intro kind name _ ok
    cases kind with
    | «local» => simp [compileExpExactHOL, exprPrices]
    | «global» =>
      rcases h : expressionValue s (.var .global name) with _ | value
      · exact absurd h ok
      have found := globals_global_value h
      obtain ⟨address, entry, wf⟩ := globalsRel_global rel found
      have length := flattenHOL_length_eq_sizeOfShapeHOL value wf
      simp only [compileExpExactHOL, entry]
      simp [exprPrices, exprListPrices, cexpHeads, valueInfo, found, globalAddressPrice, length]
  · intro fields ih ready ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) fields ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]; rfl
    have smaller := ih (by simpa [globalsReadyExp] using ready) children
    simp only [compileExpExactHOL, exprPrices, smaller]
  · intro index value ih ready ok
    have child : expressionValue s value ≠ none := by
      intro h; apply ok; simp only [expressionValue] at h ⊢; rw [evalHOLExact, h]
    have smaller := ih (by simpa [globalsReadyExp] using ready) child
    simp only [compileExpExactHOL, exprPrices, smaller]
  · intro name fields _ ready _
    simp [globalsReadyExp] at ready
  · intro name value _ ready _
    simp [globalsReadyExp] at ready
  · intro shape address ih ready ok
    obtain ⟨_, w, hw⟩ := sharp_value_some_load ok
    have smaller := ih (by simpa [globalsReadyExp] using ready) (by rw [hw]; simp)
    simp only [compileExpExactHOL, exprPrices, smaller]
  · intro address ih ready ok
    obtain ⟨w, hw⟩ := sharp_value_some_word_child (Or.inl rfl) ok
    have smaller := ih (by simpa [globalsReadyExp] using ready) (by rw [hw]; simp)
    simp only [compileExpExactHOL, exprPrices, smaller]
  · intro address ih ready ok
    obtain ⟨w, hw⟩ := sharp_value_some_word_child (Or.inr rfl) ok
    have smaller := ih (by simpa [globalsReadyExp] using ready) (by rw [hw]; simp)
    simp only [compileExpExactHOL, exprPrices, smaller]
  · intro operator args ih ready ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]
    have smaller := ih (by simpa [globalsReadyExp] using ready) children
    simp only [compileExpExactHOL, exprPrices, smaller]
  · intro operator args ih ready ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]
    have smaller := ih (by simpa [globalsReadyExp] using ready) children
    simp only [compileExpExactHOL, exprPrices, smaller]
  · intro operator left right ihLeft ihRight ready ok
    simp only [globalsReadyExp, Bool.and_eq_true] at ready
    have both : expressionValue s left ≠ none ∧ expressionValue s right ≠ none := by
      constructor <;> intro h <;> apply ok <;> simp only [expressionValue] at h ⊢ <;>
        rw [evalHOLExact] <;> simp [h]
    simp only [compileExpExactHOL, exprPrices, ihLeft ready.1 both.1, ihRight ready.2 both.2]
  · intro operator left right ihLeft ihRight ready ok
    simp only [globalsReadyExp, Bool.and_eq_true] at ready
    have both : expressionValue s left ≠ none ∧ expressionValue s right ≠ none := by
      constructor <;> intro h <;> apply ok <;> simp only [expressionValue] at h ⊢ <;>
        rw [evalHOLExact] <;> simp [h]
    simp only [compileExpExactHOL, exprPrices, ihLeft ready.1 both.1, ihRight ready.2 both.2]
  · intros
    simp [compileExpExactHOL, exprPrices]
  · intro ready _
    simp [globalsReadyExp] at ready
  · intros
    simp [compileExpExactHOL, exprPrices]
  · intros
    simp [compileExpExactHOLList, exprListPrices]
  · intro head tail ihHead ihTail ready ok
    simp only [globalsReadyExps, Bool.and_eq_true] at ready
    have both := globals_list_ok ok
    simp only [compileExpExactHOLList, exprListPrices, ihHead ready.1 both.1, ihTail ready.2 both.2]
  · trivial
  · intros; trivial
  · intros; trivial

/-- Every `pan_globals`-ready successful expression: the compiled expression's
sharp score is at most the source expression's (they are equal). -/
theorem globals_expression_le {F : Type} (B : Nat) {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    (e : ExpHOL 64) (ready : globalsReadyExp e = true) (ok : expressionValue s e ≠ none) :
    sharpSourceScore B (expressionEvents t (compileExpExactHOL context e)) ≤
      sharpSourceScore B (expressionEvents s e) := by
  rw [srcScore_expressionEvents, srcScore_expressionEvents]
  simp only [sourcePrice, sourcePrices, ← globals_locals_eq rel, globals_exprPrices_eq rel e ready ok]
  exact Nat.le_refl _

#print axioms globals_exprPrices_eq
#print axioms globals_expression_le
end InitECandidate.Runtime.FineCost
