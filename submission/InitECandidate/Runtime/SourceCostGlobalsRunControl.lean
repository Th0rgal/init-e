import InitECandidate.Runtime.SourceCostGlobalsRunBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem globals_compile_ite (context : PanGlobalsContextExact 64) (e : ExpHOL 64) (a b : ProgHOL 64) :
    compileProgExactHOL context (.ite e a b) =
      .ite (compileExpExactHOL context e) (compileProgExactHOL context a) (compileProgExactHOL context b) := by
  simp [compileProgExactHOL]

theorem globals_compile_while (context : PanGlobalsContextExact 64) (e : ExpHOL 64) (body : ProgHOL 64) :
    compileProgExactHOL context (.while e body) =
      .while (compileExpExactHOL context e) (compileProgExactHOL context body) := by
  simp [compileProgExactHOL]

/-- A guard evaluated on both sides: the compiled guard has the same word and
no larger sharp score. -/
theorem globals_guard (B : Nat) {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    {e : ExpHOL 64} {w : BitVec 64} {ev ev' : List WorkEvent} {value' : Option (ValueHOL 64)}
    (src : CostedExpressionRun s e (some (.val (.word w))) ev)
    (tgt : CostedExpressionRun t (compileExpExactHOL context e) value' ev')
    (ready : globalsReadyExp e = true) :
    value' = some (.val (.word w)) ∧ sharpSourceScore B ev' ≤ sharpSourceScore B ev :=
  globals_costed B rel src tgt ready

theorem globals_word_inj {a b : BitVec 64}
    (h : (some (.val (.word a)) : Option (ValueHOL 64)) = some (.val (.word b))) : a = b := by
  simpa using h

theorem globals_iteYes (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {yes no : ProgHOL 64} {value : BitVec 64} {guardEvents r bodyEvents}
    (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
    (nonzero : value ≠ 0) (body : StatementRun s yes r post bodyEvents)
    (ih : GlobalsLe B s yes r post bodyEvents) :
    GlobalsLe B s (.ite condition yes no) r post (.statement :: (guardEvents ++ bodyEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  rw [globals_compile_ite] at target
  cases target with
  | iteYes guard' _ body' =>
    obtain ⟨_, g⟩ := globals_guard B rel guard guard' ready.1.1
    have b := ih context t rel ok ready.1.2 code h cov _ _ _ body'
    rw [srcScore_statement, srcScore_statement, sharpSourceScore_append, sharpSourceScore_append]
    omega
  | iteNo guard' _ =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' ready.1.1
    exact absurd (globals_word_inj hv).symm nonzero
  | iteInvalidGuard guard' invalid =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' ready.1.1
    exact absurd hv (invalid _)

theorem globals_iteNo (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {yes no : ProgHOL 64} {guardEvents r bodyEvents}
    (guard : CostedExpressionRun s condition (some (.val (.word 0))) guardEvents)
    (body : StatementRun s no r post bodyEvents)
    (ih : GlobalsLe B s no r post bodyEvents) :
    GlobalsLe B s (.ite condition yes no) r post (.statement :: (guardEvents ++ bodyEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  rw [globals_compile_ite] at target
  cases target with
  | iteYes guard' nonzero _ =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' ready.1.1
    exact absurd (globals_word_inj hv) nonzero
  | iteNo guard' body' =>
    obtain ⟨_, g⟩ := globals_guard B rel guard guard' ready.1.1
    have b := ih context t rel ok ready.2 code h cov _ _ _ body'
    rw [srcScore_statement, srcScore_statement, sharpSourceScore_append, sharpSourceScore_append]
    omega
  | iteInvalidGuard guard' invalid =>
    obtain ⟨hv, _⟩ := globals_guard B rel guard guard' ready.1.1
    exact absurd hv (invalid _)

#print axioms globals_iteYes
#print axioms globals_iteNo
end InitECandidate.Runtime.FineCost
