import CandidateMemcpyShape

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open InitECandidate.Proofs.FrontendCodecComputation
open Flapjack.Basis.Pure.MlString

/-- Actual 32-byte copy iteration split into its four stores and bump. -/
theorem candidateMemcpyStep32_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s memcpyStep32 none post events) :
    ∃ (s1 s2 s3 s4 : PanSemStateFiniteExact 64 F)
      (e0 e8 e16 e24 bump : List WorkEvent),
      events = e0 ++ (e8 ++ (e16 ++ (e24 ++ bump))) ∧
      StatementRun fn s memcpyStoreWord0 none s1 e0 ∧
      StatementRun fn s1 (.store (ato "dst" "i" 8) (lw (ato "src" "i" 8)))
        none s2 e8 ∧
      StatementRun fn s2 (.store (ato "dst" "i" 16) (lw (ato "src" "i" 16)))
        none s3 e16 ∧
      StatementRun fn s3 (.store (ato "dst" "i" 24) (lw (ato "src" "i" 24)))
        none s4 e24 ∧
      StatementRun fn s4 memcpyBump32 none post bump := by
  rw [candidateMemcpy_step32] at run
  cases run with
  | seqNext store0 rest =>
      cases rest with
      | seqNext store8 rest8 =>
          cases rest8 with
          | seqNext store16 rest16 =>
              cases rest16 with
              | seqNext store24 bumpRun =>
                  exact ⟨_, _, _, _, _, _, _, _, _, rfl,
                    store0, store8, store16, store24, bumpRun⟩
              | seqStop terminal _ => exact absurd rfl terminal
          | seqStop terminal _ => exact absurd rfl terminal
      | seqStop terminal _ => exact absurd rfl terminal
  | seqStop terminal _ => exact absurd rfl terminal

/-- Actual score of a 32-byte copy iteration is additive over its parts. -/
theorem candidateMemcpyStep32_score {F : Type} (coeff : Work)
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s memcpyStep32 none post events) :
    ∃ e0 e8 e16 e24 bump : List WorkEvent,
      events = e0 ++ (e8 ++ (e16 ++ (e24 ++ bump))) ∧
      coeff.score (executionWork events) =
        coeff.score (executionWork e0) + coeff.score (executionWork e8) +
        coeff.score (executionWork e16) + coeff.score (executionWork e24) +
        coeff.score (executionWork bump) := by
  obtain ⟨_, _, _, _, e0, e8, e16, e24, bump, rfl, _, _, _, _, _⟩ :=
    candidateMemcpyStep32_trace run
  refine ⟨e0, e8, e16, e24, bump, rfl, ?_⟩
  rw [executionWork_score_append, executionWork_score_append,
    executionWork_score_append, executionWork_score_append]
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateMemcpyStep32_trace
#print axioms BoundedTableExperiment.candidateMemcpyStep32_score
