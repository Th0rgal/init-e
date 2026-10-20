import InitECandidate.Runtime.SourceCostGlobalsExpr
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem globals_global_value {F : Type} {s : PanSemStateFiniteExact 64 F} {name} {value : ValueHOL 64}
    (h : expressionValue s (.var .global name) = some value) : s.globals.lookup name = some value := by
  simpa [expressionValue, evalHOLExact] using h

/-- A global read: the compiled `TopAddr` load is paid by the source copy and
its `globalAccess` event. -/
theorem globals_var_global_le {F : Type} (B : Nat) {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    (name : MlStringHOL) (ok : expressionValue s (.var .global name) ≠ none) :
    sharpSourceScore B (expressionEvents t (compileExpExactHOL context (.var .global name))) ≤
      sharpSourceScore B (expressionEvents s (.var .global name)) := by
  rcases h : expressionValue s (.var .global name) with _ | value
  · exact absurd h ok
  obtain ⟨address, found, wf⟩ := globalsRel_global rel (globals_global_value h)
  have words := globals_resultWords rel ok
  have sourceWords : resultWords s (.var .global name) = (flattenHOL value).length := by
    simp [resultWords, h]
  have length := flattenHOL_length_eq_sizeOfShapeHOL value wf
  have size : sizeOfShapeWithContextHOL t.structs (shapeOfHOLExact value) = (flattenHOL value).length := by
    rw [globalsRel_targetStructs rel, sharp_size_nil, length]
  have compiled : compileExpExactHOL context (.var .global name) =
      .load (shapeOfHOLExact value) (.op .sub [.topAddr, .const address]) := by
    simp [compileExpExactHOL, found]
  rw [compiled] at words ⊢
  have address_score := globals_address_score B t address
  conv => rhs; rw [expressionEvents]
  simp only [globalEvents, srcScore_expression B, srcScore_copy B, srcScore_global B, sharpSourceScore_nil B]
  rw [expressionEvents]
  split
  · split
    · simp only [srcScore_expression B, sharpSourceScore_append B, srcScore_memory B, srcScore_copy B,
        sharpSourceScore_nil B, size, words, sourceWords]
      omega
    · simp only [srcScore_expression B, sharpSourceScore_append B, sharpSourceScore_nil B]
      omega
  · simp only [srcScore_expression B, sharpSourceScore_nil B]
    omega

#print axioms globals_var_global_le

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

/-- Every `pan_globals`-ready successful expression: the compiled expression's
sharp score is at most the source expression's. -/
theorem globals_expression_le {F : Type} (B : Nat) {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t) :
    ∀ e : ExpHOL 64, globalsReadyExp e = true → expressionValue s e ≠ none →
      sharpSourceScore B (expressionEvents t (compileExpExactHOL context e)) ≤
        sharpSourceScore B (expressionEvents s e) := by
  have sourceStructs : s.structs = [] := by
    unfold panGlobalsStateRelHOLExact at rel; exact rel.2.2.2.2.2.2.1
  have targetStructs := globalsRel_targetStructs rel
  refine ExpHOL.rec
    (motive_1 := fun e => globalsReadyExp e = true → expressionValue s e ≠ none →
      sharpSourceScore B (expressionEvents t (compileExpExactHOL context e)) ≤
        sharpSourceScore B (expressionEvents s e))
    (motive_2 := fun es => globalsReadyExps es = true →
      @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es ≠ none →
      sharpSourceScore B (expressionListEvents t (compileExpExactHOLList context es)) ≤
        sharpSourceScore B (expressionListEvents s es))
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value _ _
    simp only [compileExpExactHOL]; rw [expressionEvents, expressionEvents]; exact Nat.le_refl _
  · intro kind name _ ok
    cases kind with
    | «local» =>
      have words := globals_resultWords rel ok
      simp only [compileExpExactHOL] at words ⊢
      rw [expressionEvents, expressionEvents, words]
      exact Nat.le_refl _
    | «global» => exact globals_var_global_le B rel name ok
  · intro fields ih ready ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) fields ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]; rfl
    have smaller := ih (by simpa [globalsReadyExp] using ready) children
    have words := globals_resultWords rel ok
    simp only [compileExpExactHOL] at words ⊢
    rw [expressionEvents, expressionEvents, words]
    simp only [srcScore_expression B, sharpSourceScore_append B, srcScore_copy B, sharpSourceScore_nil B]
    omega
  · intro index value ih ready ok
    have child : expressionValue s value ≠ none := by
      intro h; apply ok; simp only [expressionValue] at h ⊢; rw [evalHOLExact, h]
    have smaller := ih (by simpa [globalsReadyExp] using ready) child
    have words := globals_resultWords rel ok
    simp only [compileExpExactHOL] at words ⊢
    rw [expressionEvents, expressionEvents, words]
    simp only [srcScore_expression B, sharpSourceScore_append B, srcScore_copy B, sharpSourceScore_nil B]
    omega
  · intro name fields _ ready _
    simp [globalsReadyExp] at ready
  · intro name value _ ready _
    simp [globalsReadyExp] at ready
  · intro shape address ih ready ok
    obtain ⟨wf, w, hw⟩ := sharp_value_some_load ok
    have smaller := ih (by simpa [globalsReadyExp] using ready) (by rw [hw]; simp)
    have isWord := globals_isWord rel (e := address) (by rw [hw]; simp)
    have words := globals_resultWords rel ok
    simp only [compileExpExactHOL] at words ⊢
    rw [expressionEvents, expressionEvents, words, isWord, targetStructs, ← sourceStructs]
    simp only [wf, sharp_isWord hw, ↓reduceIte, srcScore_expression B, sharpSourceScore_append B,
      srcScore_memory B, srcScore_copy B, sharpSourceScore_nil B]
    omega
  · intro address ih ready ok
    obtain ⟨w, hw⟩ := sharp_value_some_word_child (Or.inl rfl) ok
    have smaller := ih (by simpa [globalsReadyExp] using ready) (by rw [hw]; simp)
    have isWord := globals_isWord rel (e := address) (by rw [hw]; simp)
    have words := globals_resultWords rel ok
    simp only [compileExpExactHOL] at words ⊢
    rw [expressionEvents, expressionEvents, words, isWord]
    simp only [sharp_isWord hw, ↓reduceIte, srcScore_expression B, sharpSourceScore_append B,
      srcScore_memory B, srcScore_copy B, sharpSourceScore_nil B]
    omega
  · intro address ih ready ok
    obtain ⟨w, hw⟩ := sharp_value_some_word_child (Or.inr rfl) ok
    have smaller := ih (by simpa [globalsReadyExp] using ready) (by rw [hw]; simp)
    have isWord := globals_isWord rel (e := address) (by rw [hw]; simp)
    have words := globals_resultWords rel ok
    simp only [compileExpExactHOL] at words ⊢
    rw [expressionEvents, expressionEvents, words, isWord]
    simp only [sharp_isWord hw, ↓reduceIte, srcScore_expression B, sharpSourceScore_append B,
      srcScore_memory B, srcScore_copy B, sharpSourceScore_nil B]
    omega
  · intro operator args ih ready ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]
    have smaller := ih (by simpa [globalsReadyExp] using ready) children
    simp only [compileExpExactHOL]
    rw [expressionEvents, expressionEvents]
    simp only [srcScore_expression B, sharpSourceScore_append B, srcScore_scalar B, sharpSourceScore_nil B]
    omega
  · intro operator args ih ready ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]
    have smaller := ih (by simpa [globalsReadyExp] using ready) children
    simp only [compileExpExactHOL]
    rw [expressionEvents, expressionEvents]
    simp only [srcScore_expression B, sharpSourceScore_append B, srcScore_scalar B, sharpSourceScore_nil B]
    omega
  · intro operator left right ihLeft ihRight ready ok
    simp only [globalsReadyExp, Bool.and_eq_true] at ready
    have both : expressionValue s left ≠ none ∧ expressionValue s right ≠ none := by
      constructor <;> intro h <;> apply ok <;> simp only [expressionValue] at h ⊢ <;>
        rw [evalHOLExact] <;> simp [h]
    have a := ihLeft ready.1 both.1
    have b := ihRight ready.2 both.2
    simp only [compileExpExactHOL]
    rw [expressionEvents, expressionEvents, globals_isWord rel both.1, globals_isWord rel both.2]
    simp only [srcScore_expression B, sharpSourceScore_append B]
    split <;> simp only [srcScore_scalar B, sharpSourceScore_nil B] <;> omega
  · intro operator left right ihLeft ihRight ready ok
    simp only [globalsReadyExp, Bool.and_eq_true] at ready
    have both : expressionValue s left ≠ none ∧ expressionValue s right ≠ none := by
      constructor <;> intro h <;> apply ok <;> simp only [expressionValue] at h ⊢ <;>
        rw [evalHOLExact] <;> simp [h]
    have a := ihLeft ready.1 both.1
    have b := ihRight ready.2 both.2
    simp only [compileExpExactHOL]
    rw [expressionEvents, expressionEvents, globals_isWord rel both.1, globals_isWord rel both.2]
    simp only [srcScore_expression B, sharpSourceScore_append B]
    split <;> simp only [srcScore_scalar B, sharpSourceScore_nil B] <;> omega
  · intros
    simp only [compileExpExactHOL]; rw [expressionEvents, expressionEvents]; exact Nat.le_refl _
  · intro ready _
    simp [globalsReadyExp] at ready
  · intros
    simp only [compileExpExactHOL]; rw [expressionEvents, expressionEvents]; exact Nat.le_refl _
  · intros
    simp [compileExpExactHOLList, expressionListEvents]
  · intro head tail ihHead ihTail ready ok
    simp only [globalsReadyExps, Bool.and_eq_true] at ready
    have both := globals_list_ok ok
    have a := ihHead ready.1 both.1
    have b := ihTail ready.2 both.2
    simp only [compileExpExactHOLList]
    rw [expressionListEvents, expressionListEvents, sharpSourceScore_append B, sharpSourceScore_append B]
    omega
  · trivial
  · intros; trivial
  · intros; trivial

#print axioms globals_expression_le
end InitECandidate.Runtime.FineCost
