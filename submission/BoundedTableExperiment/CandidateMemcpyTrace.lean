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

/-- Actual unaligned 8-byte copy iteration: eight byte stores plus bump. -/
theorem candidateMemcpyStep8Bytes_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s memcpyStep8Bytes none post events) :
    ∃ (s1 s2 s3 s4 s5 s6 s7 s8 : PanSemStateFiniteExact 64 F)
      (e0 e1 e2 e3 e4 e5 e6 e7 bump : List WorkEvent),
      events = e0 ++ (e1 ++ (e2 ++ (e3 ++ (e4 ++ (e5 ++ (e6 ++ (e7 ++ bump))))))) ∧
      StatementRun fn s memcpyStoreByte0 none s1 e0 ∧
      StatementRun fn s1 (memcpyStoreByte 1) none s2 e1 ∧
      StatementRun fn s2 (memcpyStoreByte 2) none s3 e2 ∧
      StatementRun fn s3 (memcpyStoreByte 3) none s4 e3 ∧
      StatementRun fn s4 (memcpyStoreByte 4) none s5 e4 ∧
      StatementRun fn s5 (memcpyStoreByte 5) none s6 e5 ∧
      StatementRun fn s6 (memcpyStoreByte 6) none s7 e6 ∧
      StatementRun fn s7 (memcpyStoreByte 7) none s8 e7 ∧
      StatementRun fn s8 memcpyBump8 none post bump := by
  rw [show memcpyStep8Bytes = .seq memcpyStoreByte0
    (.seq (memcpyStoreByte 1)
      (.seq (memcpyStoreByte 2)
        (.seq (memcpyStoreByte 3)
          (.seq (memcpyStoreByte 4)
            (.seq (memcpyStoreByte 5) (.seq (memcpyStoreByte 6) (.seq (memcpyStoreByte 7) memcpyBump8)))))))
    from rfl] at run
  cases run with
  | seqNext b0 r0 =>
    cases r0 with
    | seqNext b1 r1 =>
      cases r1 with
      | seqNext b2 r2 =>
        cases r2 with
        | seqNext b3 r3 =>
          cases r3 with
          | seqNext b4 r4 =>
            cases r4 with
            | seqNext b5 r5 =>
              cases r5 with
              | seqNext b6 r6 =>
                cases r6 with
                | seqNext b7 bumpRun =>
                  exact ⟨_,_,_,_,_,_,_,_, _,_,_,_,_,_,_,_,_, rfl,
                    b0,b1,b2,b3,b4,b5,b6,b7,bumpRun⟩
                | seqStop t _ => exact absurd rfl t
              | seqStop t _ => exact absurd rfl t
            | seqStop t _ => exact absurd rfl t
          | seqStop t _ => exact absurd rfl t
        | seqStop t _ => exact absurd rfl t
      | seqStop t _ => exact absurd rfl t
    | seqStop t _ => exact absurd rfl t
  | seqStop t _ => exact absurd rfl t

/-- Actual aligned 8-byte copy iteration: one word store plus bump. -/
theorem candidateMemcpyWhile8_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s (.seq memcpyStoreWord0 memcpyBump8) none post events) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (storeEvents bumpEvents : List WorkEvent),
      events = storeEvents ++ bumpEvents ∧
      StatementRun fn s memcpyStoreWord0 none mid storeEvents ∧
      StatementRun fn mid memcpyBump8 none post bumpEvents := by
  cases run with
  | seqNext storeRun bumpRun => exact ⟨_, _, _, rfl, storeRun, bumpRun⟩
  | seqStop t _ => exact absurd rfl t

/-- Actual byte-loop iteration: one byte store plus bump. -/
theorem candidateMemcpyWhileByte_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s (.seq memcpyStoreByte0 memcpyBump1) none post events) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (storeEvents bumpEvents : List WorkEvent),
      events = storeEvents ++ bumpEvents ∧
      StatementRun fn s memcpyStoreByte0 none mid storeEvents ∧
      StatementRun fn mid memcpyBump1 none post bumpEvents := by
  cases run with
  | seqNext storeRun bumpRun => exact ⟨_, _, _, rfl, storeRun, bumpRun⟩
  | seqStop t _ => exact absurd rfl t

/-- Actual score of the aligned 8-byte iteration is additive. -/
theorem candidateMemcpyWhile8_score {F : Type} (coeff : Work)
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s (.seq memcpyStoreWord0 memcpyBump8) none post events) :
    ∃ storeEvents bumpEvents : List WorkEvent,
      events = storeEvents ++ bumpEvents ∧
      coeff.score (executionWork events) =
        coeff.score (executionWork storeEvents) +
        coeff.score (executionWork bumpEvents) := by
  obtain ⟨_, storeEvents, bumpEvents, rfl, _, _⟩ := candidateMemcpyWhile8_trace run
  exact ⟨storeEvents, bumpEvents, rfl, executionWork_score_append coeff _ _⟩

/-- Actual score of the byte-loop iteration is additive. -/
theorem candidateMemcpyWhileByte_score {F : Type} (coeff : Work)
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s (.seq memcpyStoreByte0 memcpyBump1) none post events) :
    ∃ storeEvents bumpEvents : List WorkEvent,
      events = storeEvents ++ bumpEvents ∧
      coeff.score (executionWork events) =
        coeff.score (executionWork storeEvents) +
        coeff.score (executionWork bumpEvents) := by
  obtain ⟨_, storeEvents, bumpEvents, rfl, _, _⟩ := candidateMemcpyWhileByte_trace run
  exact ⟨storeEvents, bumpEvents, rfl, executionWork_score_append coeff _ _⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateMemcpyStep32_trace
#print axioms BoundedTableExperiment.candidateMemcpyStep32_score
#print axioms BoundedTableExperiment.candidateMemcpyStep8Bytes_trace
#print axioms BoundedTableExperiment.candidateMemcpyWhile8_trace
#print axioms BoundedTableExperiment.candidateMemcpyWhileByte_trace
#print axioms BoundedTableExperiment.candidateMemcpyWhile8_score
#print axioms BoundedTableExperiment.candidateMemcpyWhileByte_score
