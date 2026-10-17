import InitECandidate.Runtime.MemeqWordLoopSteps
import InitECandidate.Runtime.StraightLineNoTimeout
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ZeroClockNormalIdentity {F : Type} (program : ProgHOL 64) : Prop :=
  ∀ state : PanSemStateFiniteExact 64 F,
    (evaluateHOLFiniteState state program).2.clock = state.clock ∧
    (evaluateHOLFiniteState state program).1 ≠ some .timeOut ∧
    ((evaluateHOLFiniteState state program).1 = none → (evaluateHOLFiniteState state program).2 = state)

theorem memeqChecks_straightLine (checks : List (ExpHOL 64 × ExpHOL 64)) :
    straightLine (memeqChecks checks) = true := by
  induction checks with
  | nil => rfl
  | cons pair rest ih => simpa [memeqChecks,straightLine] using ih

theorem evaluate_memeqChecks_terminal {F : Type} (checks : List (ExpHOL 64 × ExpHOL 64))
    (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (memeqChecks checks)).1 ≠ none := by
  induction checks generalizing state with
  | nil => simp [memeqChecks,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  | cons pair rest ih =>
    exact evaluate_sequence_terminal state _ _ ih

theorem zeroClockNormalIdentity_check {F : Type} (condition : ExpHOL 64)
    (checks : List (ExpHOL 64 × ExpHOL 64)) :
    ZeroClockNormalIdentity (F := F) (.ite condition (memeqChecks checks) .skip) := by
  intro state
  have supported : straightLine (.ite condition (memeqChecks checks) .skip) = true := by
    simp [straightLine,memeqChecks_straightLine]
  refine ⟨clockPreserving_of_straightLine _ supported state,evaluate_straightLine_no_timeout _ supported state,?_⟩
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · simp [evaluateHOLFiniteState_skip]
    · intro impossible
      exact False.elim (evaluate_memeqChecks_terminal checks state impossible)
  · simp

theorem zeroClockNormalIdentity_seq {F : Type} (first second : ProgHOL 64)
    (one : ZeroClockNormalIdentity (F := F) first) (two : ZeroClockNormalIdentity (F := F) second) :
    ZeroClockNormalIdentity (F := F) (.seq first second) := by
  intro state
  have firstFacts := one state
  refine ⟨evaluate_sequence_preserves_clock state first second firstFacts.1 (fun next => (two next).1),
    evaluate_sequence_no_timeout state first second firstFacts.2.1 (fun next => (two next).2.1),?_⟩
  cases run : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [run] at firstFacts
    dsimp only at firstFacts
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      dsimp only
      rw [firstFacts.2.2 rfl]
      exact (two state).2.2
    | some result => simp

def memeqFastPrefix : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "n")) (.const 20)) memeqFast20 .skip)
    (.seq (.ite (.cmp .equal (.var .local (ofString "n")) (.const 32)) memeqFast32 .skip)
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const 52)) memeqFast52 .skip))

theorem memeq_fast_prefix_frame {F : Type} : ZeroClockNormalIdentity (F := F) memeqFastPrefix := by
  unfold memeqFastPrefix
  rw [source_memeq_fast20,source_memeq_fast32,source_memeq_fast52]
  exact zeroClockNormalIdentity_seq _ _ (zeroClockNormalIdentity_check _ _)
    (zeroClockNormalIdentity_seq _ _ (zeroClockNormalIdentity_check _ _) (zeroClockNormalIdentity_check _ _))

#print axioms memeqChecks_straightLine
#print axioms evaluate_memeqChecks_terminal
#print axioms zeroClockNormalIdentity_check
#print axioms zeroClockNormalIdentity_seq
#print axioms memeq_fast_prefix_frame
end InitECandidate.Runtime
