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

/-- Actual 32-byte zeroing iteration split into four zero stores and bump. -/
theorem candidateMemzeroStep32_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s memzeroStep32 none post events) :
    ∃ (s1 s2 s3 s4 : PanSemStateFiniteExact 64 F)
      (e0 e8 e16 e24 bump : List WorkEvent),
      events = e0 ++ (e8 ++ (e16 ++ (e24 ++ bump))) ∧
      StatementRun fn s memzeroStoreWord0 none s1 e0 ∧
      StatementRun fn s1 (.store (ato "dst" "i" 8) (.const 0)) none s2 e8 ∧
      StatementRun fn s2 (.store (ato "dst" "i" 16) (.const 0)) none s3 e16 ∧
      StatementRun fn s3 (.store (ato "dst" "i" 24) (.const 0)) none s4 e24 ∧
      StatementRun fn s4 memcpyBump32 none post bump := by
  rw [candidateMemzero_step32] at run
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

/-- Actual aligned 8-byte zeroing iteration. -/
theorem candidateMemzeroWhile8_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s (.seq memzeroStoreWord0 memcpyBump8) none post events) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (storeEvents bumpEvents : List WorkEvent),
      events = storeEvents ++ bumpEvents ∧
      StatementRun fn s memzeroStoreWord0 none mid storeEvents ∧
      StatementRun fn mid memcpyBump8 none post bumpEvents := by
  cases run with
  | seqNext storeRun bumpRun => exact ⟨_, _, _, rfl, storeRun, bumpRun⟩
  | seqStop t _ => exact absurd rfl t

/-- Actual byte-loop zeroing iteration. -/
theorem candidateMemzeroWhileByte_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s (.seq memzeroStoreByte0 memcpyBump1) none post events) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (storeEvents bumpEvents : List WorkEvent),
      events = storeEvents ++ bumpEvents ∧
      StatementRun fn s memzeroStoreByte0 none mid storeEvents ∧
      StatementRun fn mid memcpyBump1 none post bumpEvents := by
  cases run with
  | seqNext storeRun bumpRun => exact ⟨_, _, _, rfl, storeRun, bumpRun⟩
  | seqStop t _ => exact absurd rfl t

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateMemzeroStep32_trace
#print axioms BoundedTableExperiment.candidateMemzeroWhile8_trace
#print axioms BoundedTableExperiment.candidateMemzeroWhileByte_trace
