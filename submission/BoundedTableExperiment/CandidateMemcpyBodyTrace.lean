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

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateMemcpy_body_trace
