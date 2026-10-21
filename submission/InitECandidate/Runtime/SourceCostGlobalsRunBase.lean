import InitECandidate.Runtime.SourceCostGlobalsDomain
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! `pan_globals` statement transfer: every compiled run from a related state
costs no more, under `sharpSourceScore B`, than the source run. The target run
is inverted; its results and intermediate states are matched to the source run
through the original `compile_correct` and determinism. -/

/-- Every global laid out by `pan_globals` is present in the source state. -/
def GlobalsCovered {F : Type} (context : PanGlobalsContextExact 64) (s : PanSemStateFiniteExact 64 F) :
    Prop :=
  ∀ name entry, context.globals.lookup name = some entry → GlobalsPresent s name

theorem StatementRun.covered {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun s p r post ev) {context : PanGlobalsContextExact 64}
    (cov : GlobalsCovered context s) : GlobalsCovered context post :=
  fun name entry found => run.globals_present name (cov name entry found)

/-- The transfer statement for one source run. -/
def GlobalsLe (B : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (r : Option (PanSemResultExact 64)) (_post : PanSemStateFiniteExact 64 F)
    (ev : List WorkEvent) : Prop :=
  ∀ (context : PanGlobalsContextExact 64) (t : PanSemStateFiniteExact 64 F),
    panGlobalsStateRelHOLExact true context s t → r ≠ some .error → globalsReadyProg p = true →
      GlobalsCodeReady s.code → s.locals.lookup globalsTemp = none → GlobalsCovered context s →
      ∀ r' t' ev', StatementRun t (compileProgExactHOL context p) r' t' ev' →
        sharpSourceScore B ev' ≤ sharpSourceScore B ev

theorem globals_costed (B : Nat) {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    {e : ExpHOL 64} {value : ValueHOL 64} {ev ev' : List WorkEvent} {value' : Option (ValueHOL 64)}
    (src : CostedExpressionRun s e (some value) ev)
    (tgt : CostedExpressionRun t (compileExpExactHOL context e) value' ev')
    (ready : globalsReadyExp e = true) :
    value' = some value ∧ sharpSourceScore B ev' ≤ sharpSourceScore B ev := by
  refine ⟨by rw [← tgt.sound, globals_value rel src.sound], ?_⟩
  rw [tgt.events_eq, src.events_eq]
  exact globals_expression_le B rel e ready (by rw [src.sound]; simp)

theorem globals_list_values {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t) :
    ∀ (es : List (ExpHOL 64)) (values : List (ValueHOL 64)),
      @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es = some values →
      @evalListHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (compileExpExactHOLList context es) = some values
  | [], values, h => by simpa [compileExpExactHOLList, evalListHOLExact] using h
  | head :: tail, values, h => by
    simp only [evalListHOLExact] at h
    split at h
    · rename_i v vs hv hvs
      have hv' := globals_value rel (e := head) hv
      have hvs' := globals_list_values rel tail vs hvs
      simp only [expressionValue] at hv'
      simp only [compileExpExactHOLList, evalListHOLExact, hv', hvs']
      exact h
    · simp at h

theorem globals_list_le (B : Nat) {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t) :
    ∀ es : List (ExpHOL 64), globalsReadyExps es = true →
      @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es ≠ none →
      sharpSourceScore B (expressionListEvents t (compileExpExactHOLList context es)) ≤
        sharpSourceScore B (expressionListEvents s es)
  | [], _, _ => by simp [compileExpExactHOLList, expressionListEvents]
  | head :: tail, ready, ok => by
    simp only [globalsReadyExps, Bool.and_eq_true] at ready
    have both := globals_list_ok ok
    have a := globals_expression_le B rel head ready.1 both.1
    have b := globals_list_le B rel tail ready.2 both.2
    simp only [compileExpExactHOLList]
    rw [expressionListEvents, expressionListEvents, sharpSourceScore_append, sharpSourceScore_append]
    omega

theorem globals_compile_seq (context : PanGlobalsContextExact 64) (a b : ProgHOL 64) :
    compileProgExactHOL context (.seq a b) =
      .seq (compileProgExactHOL context a) (compileProgExactHOL context b) := by
  simp [compileProgExactHOL]

theorem globals_seqNext (B : Nat) {F : Type} {s middle post : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64} {r left right}
    (one : StatementRun s a none middle left) (two : StatementRun middle b r post right)
    (ih1 : GlobalsLe B s a none middle left) (ih2 : GlobalsLe B middle b r post right) :
    GlobalsLe B s (.seq a b) r post (left ++ right) := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  rw [globals_compile_seq] at target
  cases target with
  | seqNext one' two' =>
    obtain ⟨_, rel1⟩ := globals_sub_match one (by simp) rel one'
    have l := ih1 context t rel (by simp) ready.1 code h cov _ _ _ one'
    have r2 := ih2 context _ rel1 ok ready.2 (by rw [one.code_eq]; exact code)
      (one.noTemp ready.1 code h) (one.covered cov) _ _ _ two'
    gsimp; omega
  | seqStop terminal one' =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) rel one'
    exact absurd hr terminal

theorem globals_seqStop (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64} {r left} (terminal : r ≠ none)
    (one : StatementRun s a r post left) (ih : GlobalsLe B s a r post left) :
    GlobalsLe B s (.seq a b) r post left := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  rw [globals_compile_seq] at target
  cases target with
  | seqNext one' _ =>
    obtain ⟨hr, _⟩ := globals_sub_match one ok rel one'
    exact absurd hr.symm terminal
  | seqStop _ one' =>
    have := ih context t rel ok ready.1 code h cov _ _ _ one'
    exact this

#print axioms globals_seqNext
#print axioms globals_seqStop
#print axioms globals_list_le
end InitECandidate.Runtime.FineCost
