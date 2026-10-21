import CandidateHtabSetBsearchTrace

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Splitting one binary-search iteration at its `mid` declaration. -/
theorem candidateHtabSetBsearchStep_mid {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateHtabSetBsearchStep none post events) :
    ∃ (value : ValueHOL 64) (initEvents bodyEvents : List WorkEvent)
      (postBody : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s
        (.shift .asr (.op .add [loc "lo",loc "hi"]) (.const 1))
        (some value) initEvents ∧
      post = { postBody with locals :=
        HolFiniteMapExact.resVarEq postBody.locals (ofString "mid", s.locals.lookup (ofString "mid")) } ∧
      StatementRun fn (setVarHOLFinite (ofString "mid") value s)
        (.dec (ofString "mr") .one (lw candidateHtabSetMrAddr)
          (.ite (.cmp .lower (loc "d") (loc "mr"))
            (.assign .local (ofString "hi") (loc "mid"))
            (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1]))))
        none postBody bodyEvents := by
  rw [show candidateHtabSetBsearchStep =
    .dec (ofString "mid") .one
      (.shift .asr (.op .add [loc "lo",loc "hi"]) (.const 1))
      (.dec (ofString "mr") .one (lw candidateHtabSetMrAddr)
        (.ite (.cmp .lower (loc "d") (loc "mr"))
          (.assign .local (ofString "hi") (loc "mid"))
          (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1]))))
    from rfl] at run
  cases run with
  | declareValue init shapeMatch bodyRun =>
      exact ⟨_, _, _, _, rfl, init, rfl, bodyRun⟩

/-- Splitting the `mid` body at its `mr` declaration. -/
theorem candidateHtabSetBsearchStep_mr {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s
      (.dec (ofString "mr") .one (lw candidateHtabSetMrAddr)
        (.ite (.cmp .lower (loc "d") (loc "mr"))
          (.assign .local (ofString "hi") (loc "mid"))
          (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1]))))
      none post events) :
    ∃ (value : ValueHOL 64) (initEvents bodyEvents : List WorkEvent)
      (postBody : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (lw candidateHtabSetMrAddr) (some value) initEvents ∧
      post = { postBody with locals :=
        HolFiniteMapExact.resVarEq postBody.locals (ofString "mr", s.locals.lookup (ofString "mr")) } ∧
      StatementRun fn (setVarHOLFinite (ofString "mr") value s)
        (.ite (.cmp .lower (loc "d") (loc "mr"))
          (.assign .local (ofString "hi") (loc "mid"))
          (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1])))
        none postBody bodyEvents := by
  cases run with
  | declareValue init shapeMatch bodyRun =>
      exact ⟨_, _, _, _, rfl, init, rfl, bodyRun⟩

/-- Splitting the `d < mr` branch of a binary-search iteration. -/
theorem candidateHtabSetBsearchStep_branch {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s
      (.ite (.cmp .lower (loc "d") (loc "mr"))
        (.assign .local (ofString "hi") (loc "mid"))
        (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1])))
      none post events) :
    ∃ (value : BitVec 64) (guardEvents branchEvents : List WorkEvent),
      events = .statement :: .cost (statementUnit + branchMoves fn) ::
        (guardEvents ++ branchEvents) ∧
      CostedExpressionRun s (.cmp .lower (loc "d") (loc "mr"))
        (some (.val (.word value))) guardEvents ∧
      ((value ≠ 0 ∧
        StatementRun fn s (.assign .local (ofString "hi") (loc "mid"))
          none post branchEvents) ∨
       (value = 0 ∧
        StatementRun fn s
          (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1]))
          none post branchEvents)) := by
  cases run with
  | iteYes guard nonzero body =>
      exact ⟨_, _, _, rfl, guard, Or.inl ⟨nonzero, body⟩⟩
  | iteNo guard body =>
      exact ⟨_, _, _, rfl, guard, Or.inr ⟨rfl, body⟩⟩

/-- Score of a declaration event trace. -/
theorem bsearchDecl_score (coeff : Work)
    (initEvents bodyEvents : List WorkEvent) :
    coeff.score (executionWork
      (.statement :: (initEvents ++ [.frame 1] ++ bodyEvents))) =
      coeff.statements + coeff.score (executionWork initEvents) +
      coeff.frameSlots + coeff.score (executionWork bodyEvents) := by
  rw [executionWork_score_cons, executionWork_score_append,
    executionWork_score_append]
  simp [executionWork, WorkEvent.units, Work.plus, Work.score]
  omega

/-- Score of a binary-search branch event trace. -/
theorem bsearchBranch_score {fn : MlS} (coeff : Work)
    (guardEvents branchEvents : List WorkEvent) :
    coeff.score (executionWork
      (.statement :: .cost (statementUnit + branchMoves fn) ::
        (guardEvents ++ branchEvents))) =
      coeff.statements + coeff.nativeCost * (statementUnit + branchMoves fn) +
      coeff.score (executionWork guardEvents) +
      coeff.score (executionWork branchEvents) := by
  rw [executionWork_score_cons, executionWork_score_cons,
    executionWork_score_append]
  simp [executionWork, WorkEvent.units, Work.score]
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateHtabSetBsearchStep_mid
#print axioms BoundedTableExperiment.candidateHtabSetBsearchStep_mr
#print axioms BoundedTableExperiment.candidateHtabSetBsearchStep_branch
#print axioms BoundedTableExperiment.bsearchDecl_score
#print axioms BoundedTableExperiment.bsearchBranch_score
