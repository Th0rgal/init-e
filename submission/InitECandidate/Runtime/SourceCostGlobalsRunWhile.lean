import InitECandidate.Runtime.SourceCostGlobalsRunControl
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Loop rules of the `pan_globals` statement transfer. In every compiled
branch other than the source's, the guard word, the clock, or the body result
disagrees with the source run. -/

theorem globals_whileNext (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {body : ProgHOL 64} {value : BitVec 64} {guardEvents r}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      {middle bodyEvents restEvents}
      (one : StatementRun (decClockHOLFinite s) body none middle bodyEvents)
      (rest : StatementRun middle (.while condition body) r post restEvents)
      (ih1 : GlobalsLe B (decClockHOLFinite s) body none middle bodyEvents)
      (ih2 : GlobalsLe B middle (.while condition body) r post restEvents) :
    GlobalsLe B s (.while condition body) r post (.statement :: (guardEvents ++ bodyEvents ++ restEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  have r0 := ready
  simp only [globalsReadyProg, Bool.and_eq_true] at r0
  have relD := globalsRel_decClock rel
  have clockEq := globalsRel_clock rel
  rw [globals_compile_while] at target
  cases target with
  | whileFalse guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv).symm nonzero
  | whileMissingGuard guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    cases hv
  | whileInvalidGuard guard' invalid =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd hv (invalid _)
  | whileTimeout guard' _ clock' =>
    omega
  | whileNext guard' _ _ one' rest' =>
    obtain ⟨_, g⟩ := globals_guard B rel guard guard' r0.1
    obtain ⟨_, rel1⟩ := globals_sub_match one (by simp) relD one'
    have b := ih1 context _ relD (by simp) r0.2 code h cov _ _ _ one'
    rw [← globals_compile_while] at rest'
    have rr := ih2 context _ rel1 ok ready (by rw [one.code_eq]; exact code)
      (one.noTemp r0.2 code h) (one.covered cov) _ _ _ rest'
    simp only [srcScore_statement, sharpSourceScore_append]
    omega
  | whileContinue guard' _ _ one' _ =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
  | whileBreak guard' _ _ one' =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
  | whilePropagate guard' _ _ nb nc one' =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
    all_goals first | exact absurd rfl nb | exact absurd rfl nc
theorem globals_whileContinue (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {body : ProgHOL 64} {value : BitVec 64} {guardEvents r}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      {middle bodyEvents restEvents}
      (one : StatementRun (decClockHOLFinite s) body (some .continue) middle bodyEvents)
      (rest : StatementRun middle (.while condition body) r post restEvents)
      (ih1 : GlobalsLe B (decClockHOLFinite s) body (some .continue) middle bodyEvents)
      (ih2 : GlobalsLe B middle (.while condition body) r post restEvents) :
    GlobalsLe B s (.while condition body) r post (.statement :: (guardEvents ++ bodyEvents ++ restEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  have r0 := ready
  simp only [globalsReadyProg, Bool.and_eq_true] at r0
  have relD := globalsRel_decClock rel
  have clockEq := globalsRel_clock rel
  rw [globals_compile_while] at target
  cases target with
  | whileFalse guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv).symm nonzero
  | whileMissingGuard guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    cases hv
  | whileInvalidGuard guard' invalid =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd hv (invalid _)
  | whileTimeout guard' _ clock' =>
    omega
  | whileContinue guard' _ _ one' rest' =>
    obtain ⟨_, g⟩ := globals_guard B rel guard guard' r0.1
    obtain ⟨_, rel1⟩ := globals_sub_match one (by simp) relD one'
    have b := ih1 context _ relD (by simp) r0.2 code h cov _ _ _ one'
    rw [← globals_compile_while] at rest'
    have rr := ih2 context _ rel1 ok ready (by rw [one.code_eq]; exact code)
      (one.noTemp r0.2 code h) (one.covered cov) _ _ _ rest'
    simp only [srcScore_statement, sharpSourceScore_append]
    omega
  | whileNext guard' _ _ one' _ =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
  | whileBreak guard' _ _ one' =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
  | whilePropagate guard' _ _ nb nc one' =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
    all_goals first | exact absurd rfl nb | exact absurd rfl nc
theorem globals_whileBreak (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {body : ProgHOL 64} {value : BitVec 64} {guardEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      {bodyEvents}
      (one : StatementRun (decClockHOLFinite s) body (some .break) post bodyEvents)
      (ih1 : GlobalsLe B (decClockHOLFinite s) body (some .break) post bodyEvents) :
    GlobalsLe B s (.while condition body) none post (.statement :: (guardEvents ++ bodyEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  have r0 := ready
  simp only [globalsReadyProg, Bool.and_eq_true] at r0
  have relD := globalsRel_decClock rel
  have clockEq := globalsRel_clock rel
  rw [globals_compile_while] at target
  cases target with
  | whileFalse guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv).symm nonzero
  | whileMissingGuard guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    cases hv
  | whileInvalidGuard guard' invalid =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd hv (invalid _)
  | whileTimeout guard' _ clock' =>
    omega
  | whileBreak guard' _ _ one' =>
    obtain ⟨_, g⟩ := globals_guard B rel guard guard' r0.1
    have b := ih1 context _ relD (by simp) r0.2 code h cov _ _ _ one'
    simp only [srcScore_statement, sharpSourceScore_append]
    omega
  | whileNext guard' _ _ one' _ =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
  | whileContinue guard' _ _ one' _ =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
  | whilePropagate guard' _ _ nb nc one' =>
    obtain ⟨hr, _⟩ := globals_sub_match one (by simp) relD one'
    cases hr
    all_goals first | exact absurd rfl nb | exact absurd rfl nc
theorem globals_whilePropagate (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {body : ProgHOL 64} {value : BitVec 64} {guardEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0) {result bodyEvents}
      (notBreak : result ≠ .break) (notContinue : result ≠ .continue)
      (one : StatementRun (decClockHOLFinite s) body (some result) post bodyEvents)
      (ih1 : GlobalsLe B (decClockHOLFinite s) body (some result) post bodyEvents) :
    GlobalsLe B s (.while condition body) (some result) post (.statement :: (guardEvents ++ bodyEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  have r0 := ready
  simp only [globalsReadyProg, Bool.and_eq_true] at r0
  have relD := globalsRel_decClock rel
  have clockEq := globalsRel_clock rel
  rw [globals_compile_while] at target
  cases target with
  | whileFalse guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv).symm nonzero
  | whileMissingGuard guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    cases hv
  | whileInvalidGuard guard' invalid =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd hv (invalid _)
  | whileTimeout guard' _ clock' =>
    omega
  | whilePropagate guard' _ _ _ _ one' =>
    obtain ⟨_, g⟩ := globals_guard B rel guard guard' r0.1
    have b := ih1 context _ relD ok r0.2 code h cov _ _ _ one'
    simp only [srcScore_statement, sharpSourceScore_append]
    omega
  | whileNext guard' _ _ one' _ =>
    obtain ⟨hr, _⟩ := globals_sub_match one ok relD one'
    cases hr
  | whileContinue guard' _ _ one' _ =>
    obtain ⟨hr, _⟩ := globals_sub_match one ok relD one'
    cases hr; exact absurd rfl notContinue
  | whileBreak guard' _ _ one' =>
    obtain ⟨hr, _⟩ := globals_sub_match one ok relD one'
    cases hr; exact absurd rfl notBreak
theorem globals_whileFalse (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {body : ProgHOL 64} {guardEvents}
    (guard : CostedExpressionRun s condition (some (.val (.word 0))) guardEvents) :
    GlobalsLe B s (.while condition body) none s (.statement :: guardEvents) := by
  intro context t rel ok ready code h cov r' t' ev' target
  have r0 := ready
  simp only [globalsReadyProg, Bool.and_eq_true] at r0
  rw [globals_compile_while] at target
  cases target with
  | whileFalse guard' =>
    obtain ⟨_, g⟩ := globals_guard B rel guard guard' r0.1
    simp only [srcScore_statement]; omega
  | whileMissingGuard guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    cases hv
  | whileInvalidGuard guard' invalid =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd hv (invalid _)
  | whileTimeout guard' nonzero _ =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv) nonzero
  | whileNext guard' nonzero _ _ _ =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv) nonzero
  | whileContinue guard' nonzero _ _ _ =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv) nonzero
  | whileBreak guard' nonzero _ _ =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv) nonzero
  | whilePropagate guard' nonzero _ _ _ _ =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv) nonzero

theorem globals_whileTimeout (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {body : ProgHOL 64} {value : BitVec 64} {guardEvents}
    (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
    (nonzero : value ≠ 0) (clock : s.clock = 0) :
    GlobalsLe B s (.while condition body) (some .timeOut) (emptyLocalsHOLFinite s)
      (.statement :: guardEvents) := by
  intro context t rel ok ready code h cov r' t' ev' target
  have r0 := ready
  simp only [globalsReadyProg, Bool.and_eq_true] at r0
  have clockEq := globalsRel_clock rel
  rw [globals_compile_while] at target
  cases target with
  | whileTimeout guard' _ _ =>
    obtain ⟨_, g⟩ := globals_guard B rel guard guard' r0.1
    simp only [srcScore_statement]; omega
  | whileFalse guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd (globals_word_inj hv).symm nonzero
  | whileMissingGuard guard' =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    cases hv
  | whileInvalidGuard guard' invalid =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' r0.1
    exact absurd hv (invalid _)
  | whileNext _ _ clock' _ _ => omega
  | whileContinue _ _ clock' _ _ => omega
  | whileBreak _ _ clock' _ => omega
  | whilePropagate _ _ clock' _ _ _ => omega

#print axioms globals_whileNext
#print axioms globals_whilePropagate
#print axioms globals_whileFalse
#print axioms globals_whileTimeout
end InitECandidate.Runtime.FineCost
