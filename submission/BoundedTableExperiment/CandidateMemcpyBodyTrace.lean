import CandidateMemcpyTrace

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open InitECandidate.Proofs.FrontendCodecComputation
open Flapjack.Basis.Pure.MlString

/-- Actual `memcpy` body split at its `i := 0` declaration. -/
theorem candidateMemcpy_body_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s memcpyBody none post events) :
    ∃ (value : ValueHOL 64) (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (.const 0) (some value) initEvents ∧
      post = { bodyPost with locals :=
        HolFiniteMapExact.resVarEq bodyPost.locals (ofString "i", s.locals.lookup (ofString "i")) } ∧
      StatementRun fn (setVarHOLFinite (ofString "i") value s)
        (.seq
          (.ite (.cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0))
            (.seq memcpyWhile32 memcpyWhile8) .skip)
          (.seq memcpyWhile8Bytes (.seq memcpyWhileByte memcpyReturn)))
        none bodyPost bodyEvents := by
  rw [← candidateMemcpy_body] at run
  rw [candidateMemcpy_body_scopes] at run
  cases run with
  | declareValue init _ bodyRun =>
      exact ⟨_, _, _, _, rfl, init, rfl, bodyRun⟩

/-- Actual alignment `ite` split of the `memcpy` body. -/
theorem candidateMemcpy_align_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s
      (.ite (.cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0))
        (.seq memcpyWhile32 memcpyWhile8) .skip) none post events) :
    ∃ (value : BitVec 64) (guardEvents branchEvents : List WorkEvent),
      events = .statement :: .cost (statementUnit + branchMoves fn) ::
        (guardEvents ++ branchEvents) ∧
      CostedExpressionRun s
        (.cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0))
        (some (.val (.word value))) guardEvents ∧
      ((value ≠ 0 ∧
        StatementRun fn s (.seq memcpyWhile32 memcpyWhile8) none post branchEvents) ∨
       (value = 0 ∧
        StatementRun fn s .skip none post branchEvents)) := by
  cases run with
  | iteYes guard nonzero branch =>
      exact ⟨_, _, _, rfl, guard, Or.inl ⟨nonzero, branch⟩⟩
  | iteNo guard branch =>
      exact ⟨_, _, _, rfl, guard, Or.inr ⟨rfl, branch⟩⟩

/-- Actual body continuation after the alignment `ite`. -/
theorem candidateMemcpy_afterInit_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s
      (.seq
        (.ite (.cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0))
          (.seq memcpyWhile32 memcpyWhile8) .skip)
        (.seq memcpyWhile8Bytes (.seq memcpyWhileByte memcpyReturn)))
      none post events) :
    ∃ (mid : PanSemStateFiniteExact 64 F)
      (iteEvents restEvents : List WorkEvent),
      events = iteEvents ++ restEvents ∧
      StatementRun fn s
        (.ite (.cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0))
          (.seq memcpyWhile32 memcpyWhile8) .skip) none mid iteEvents ∧
      StatementRun fn mid
        (.seq memcpyWhile8Bytes (.seq memcpyWhileByte memcpyReturn))
        none post restEvents := by
  cases run with
  | seqNext iteRun restRun => exact ⟨_, _, _, rfl, iteRun, restRun⟩
  | seqStop terminal _ => exact absurd rfl terminal

/-- Actual `memcpy` tail: byte loop, byte loop, return. -/
theorem candidateMemcpy_rest_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s
      (.seq memcpyWhile8Bytes (.seq memcpyWhileByte memcpyReturn))
      none post events) :
    ∃ (s1 s2 : PanSemStateFiniteExact 64 F)
      (e8 eByte eReturn : List WorkEvent),
      events = e8 ++ (eByte ++ eReturn) ∧
      StatementRun fn s memcpyWhile8Bytes none s1 e8 ∧
      StatementRun fn s1 memcpyWhileByte none s2 eByte ∧
      StatementRun fn s2 memcpyReturn none post eReturn := by
  cases run with
  | seqNext loop8 rest =>
      cases rest with
      | seqNext loopByte returnRun =>
          exact ⟨_, _, _, _, _, rfl, loop8, loopByte, returnRun⟩
      | seqStop terminal _ => exact absurd rfl terminal
  | seqStop terminal _ => exact absurd rfl terminal

/-- Full actual `memcpy` body event list. -/
theorem candidateMemcpy_body_events {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s memcpyBody none post events) :
    ∃ (value : ValueHOL 64) (branchValue : BitVec 64)
      (initEvents guardEvents branchEvents restEvents : List WorkEvent),
      events = .statement :: (initEvents ++ [.frame 1] ++
        (.statement :: .cost (statementUnit + branchMoves fn) ::
          (guardEvents ++ branchEvents) ++ restEvents)) ∧
      CostedExpressionRun s (.const 0) (some value) initEvents ∧
      CostedExpressionRun (setVarHOLFinite (ofString "i") value s)
        (.cmp .equal (.op .and [.op .or [loc "dst",loc "src"],.const 7]) (.const 0))
        (some (.val (.word branchValue))) guardEvents := by
  obtain ⟨value, initEvents, bodyEvents, bodyPost, hbody, initRun, _, bodyRun⟩ :=
    candidateMemcpy_body_trace run
  obtain ⟨_, iteEvents, restEvents, hsplit, iteRun, _⟩ :=
    candidateMemcpy_afterInit_trace bodyRun
  obtain ⟨branchValue, guardEvents, branchEvents, halign, guard, _⟩ :=
    candidateMemcpy_align_trace iteRun
  refine ⟨value, branchValue, initEvents, guardEvents, branchEvents,
    restEvents, ?_, initRun, guard⟩
  rw [hbody, hsplit, halign]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateMemcpy_body_trace
#print axioms BoundedTableExperiment.candidateMemcpy_align_trace
#print axioms BoundedTableExperiment.candidateMemcpy_afterInit_trace
#print axioms BoundedTableExperiment.candidateMemcpy_rest_trace
#print axioms BoundedTableExperiment.candidateMemcpy_body_events
