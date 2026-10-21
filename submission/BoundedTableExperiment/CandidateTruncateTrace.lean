import CandidateTruncateShape

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open InitECandidate.Proofs.FrontendCodecComputation
open Flapjack.Basis.Pure.MlString

/-- Actual `htab_truncate` body: loop then `return 0`. -/
theorem candidateTruncate_body_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s truncateBody none post events) :
    ∃ (mid : PanSemStateFiniteExact 64 F)
      (loopEvents returnEvents : List WorkEvent),
      events = loopEvents ++ returnEvents ∧
      StatementRun fn s truncateWhile none mid loopEvents ∧
      StatementRun fn mid truncateReturn none post returnEvents := by
  rw [show truncateBody = .seq truncateWhile truncateReturn from rfl] at run
  cases run with
  | seqNext loopRun returnRun => exact ⟨_, _, _, rfl, loopRun, returnRun⟩
  | seqStop terminal _ => exact absurd rfl terminal

/-- Any actual successful truncate loop run. -/
theorem candidateTruncate_while_run_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s truncateWhile none post events) :
    (∃ guardEvents : List WorkEvent,
      events = .statement :: .cost (whileOverhead + loopMoves fn) :: guardEvents ∧
      CostedExpressionRun s (.cmp .lower (loc "n") (lw (off "t" 24)))
        (some (.val (.word 0))) guardEvents) ∨
    (∃ (value : BitVec 64) (middle : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents restEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents ++ restEvents) ∧
      CostedExpressionRun s (.cmp .lower (loc "n") (lw (off "t" 24)))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) truncateStep none middle bodyEvents ∧
      StatementRun fn middle truncateWhile none post restEvents) ∨
    (∃ (value : BitVec 64) (post' : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents) ∧
      CostedExpressionRun s (.cmp .lower (loc "n") (lw (off "t" 24)))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) truncateStep (some .break)
        post' bodyEvents) ∨
    (∃ (value : BitVec 64) (middle : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents restEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents ++ restEvents) ∧
      CostedExpressionRun s (.cmp .lower (loc "n") (lw (off "t" 24)))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) truncateStep (some .continue)
        middle bodyEvents ∧
      StatementRun fn middle truncateWhile none post restEvents) := by
  rw [candidateTruncate_while] at run
  cases run with
  | whileFalse guard => exact Or.inl ⟨_, rfl, guard⟩
  | whileNext guard nonzero _ one rest =>
      exact Or.inr (Or.inl ⟨_, _, _, _, _, nonzero, rfl, guard, one, rest⟩)
  | whileBreak guard nonzero _ one =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, nonzero, rfl, guard, one⟩))
  | whileContinue guard nonzero _ one rest =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, nonzero, rfl, guard, one, rest⟩))

/-- Actual truncate iteration split at its `pos` declaration. -/
theorem candidateTruncateStep_pos {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s truncateStep none post events) :
    ∃ (value : ValueHOL 64) (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (.op .sub [lw (off "t" 24),.const 1])
        (some value) initEvents ∧
      post = { bodyPost with locals :=
        HolFiniteMapExact.resVarEq bodyPost.locals (ofString "pos", s.locals.lookup (ofString "pos")) } ∧
      StatementRun fn (setVarHOLFinite (ofString "pos") value s)
        (.dec (ofString "leaf") .one (lw (idx8 (lw (off "t" 56)) (loc "pos")))
          truncateKeyCall) none bodyPost bodyEvents := by
  rw [candidateTruncate_step] at run
  cases run with
  | declareValue init _ bodyRun =>
      exact ⟨_, _, _, _, rfl, init, rfl, bodyRun⟩

/-- Actual truncate iteration split at its `leaf` declaration. -/
theorem candidateTruncateStep_leaf {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s
      (.dec (ofString "leaf") .one (lw (idx8 (lw (off "t" 56)) (loc "pos")))
        truncateKeyCall) none post events) :
    ∃ (value : ValueHOL 64) (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (lw (idx8 (lw (off "t" 56)) (loc "pos")))
        (some value) initEvents ∧
      post = { bodyPost with locals :=
        HolFiniteMapExact.resVarEq bodyPost.locals (ofString "leaf", s.locals.lookup (ofString "leaf")) } ∧
      StatementRun fn (setVarHOLFinite (ofString "leaf") value s)
        truncateKeyCall none bodyPost bodyEvents := by
  cases run with
  | declareValue init _ bodyRun =>
      exact ⟨_, _, _, _, rfl, init, rfl, bodyRun⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateTruncate_body_trace
#print axioms BoundedTableExperiment.candidateTruncate_while_run_split
#print axioms BoundedTableExperiment.candidateTruncateStep_pos
#print axioms BoundedTableExperiment.candidateTruncateStep_leaf
