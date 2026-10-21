import InitECandidate.Runtime.WordExecutionReturningCost
import InitECandidate.Runtime.WordStackHandlerMotive
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- Actual source-call facts specialize dynamic-cost induction hypotheses to
fixed callee and continuation budgets without charging an unexecuted branch. -/
theorem selectedReturningHandlerMotive {F : Type}
    (targetPrice : StackLang.HolProg 64 → Nat)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (ac : AsmConfigExact 64)
    (values : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (bodyResult : Option (WordSemResult 64))
    (bodyPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (bodyRun : evaluate prog (callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (decClock source))) =
      (bodyResult,bodyPost))
    (bodyIH : ExecutedSimulationFor targetPrice ac prog
      (callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (decClock source)))
      (factor * wordExecutionCost price prog (callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (decClock source)))))
    (returnIH : ∀ location returned post popped,
      evaluate prog (callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (decClock source))) =
        (some (.result location returned),post) →
      ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) →
      popEnv post = some popped → sptDomainEqUnion popped.locals envs.1 envs.2 →
      ExecutedSimulationFor targetPrice ac retCode (setVars values returned popped)
        (factor * wordExecutionCost price retCode (setVars values returned popped)))
    (handlerIH : ∀ location value post,
      evaluate prog (callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (decClock source))) =
        (some (.exception location value),post) →
      ¬ location ≠ .loc h1 h2 → sptDomainEqUnion post.locals envs.1 envs.2 →
      ExecutedSimulationFor targetPrice ac handlerCode (setVar handlerVar value post)
        (factor * wordExecutionCost price handlerCode (setVar handlerVar value post))) :
    InductionHypotheses targetPrice
      (factor * wordExecutionCost price prog (callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (decClock source))))
      (factor * wordReturningContinuationCost price values retCode l1 l2 (some (handlerVar,handlerCode,h1,h2)) envs bodyResult bodyPost)
      (factor * wordReturningContinuationCost price values retCode l1 l2 (some (handlerVar,handlerCode,h1,h2)) envs bodyResult bodyPost)
      ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source := by
  refine ⟨?_,?_,?_⟩
  · intro otherXs otherArgs otherProg otherSs otherEnvs location returned post popped facts
    rcases facts with ⟨otherGuards,nonzero,otherRun,valid,pop,domain⟩
    obtain ⟨eqXs,eqArgs,eqProg,eqSs,eqEnvs⟩ := returningSourceGuards_unique values names retCode l1 l2 dest args
      source xs args1 otherXs otherArgs prog otherProg ss otherSs envs otherEnvs guards otherGuards
    subst otherXs otherArgs otherProg otherSs otherEnvs
    have resultEq := Prod.mk.inj (bodyRun.symm.trans otherRun)
    rw [resultEq.1,resultEq.2]
    rw [wordReturningContinuationCost_normal price values retCode l1 l2 (some (handlerVar,handlerCode,h1,h2)) envs location returned
      post popped valid pop domain]
    exact returnIH location returned post popped otherRun valid pop domain
  · intro otherXs otherArgs otherProg otherSs otherEnvs location value post facts
    rcases facts with ⟨otherGuards,nonzero,otherRun,valid,domain⟩
    obtain ⟨eqXs,eqArgs,eqProg,eqSs,eqEnvs⟩ := returningSourceGuards_unique values names retCode l1 l2 dest args
      source xs args1 otherXs otherArgs prog otherProg ss otherSs envs otherEnvs guards otherGuards
    subst otherXs otherArgs otherProg otherSs otherEnvs
    have resultEq := Prod.mk.inj (bodyRun.symm.trans otherRun)
    rw [resultEq.1,resultEq.2]
    rw [wordReturningContinuationCost_exception price values retCode handlerCode l1 l2 handlerVar h1 h2 envs
      location value post valid domain]
    exact handlerIH location value post otherRun valid domain
  · intro otherXs otherArgs otherProg otherSs otherEnvs facts
    obtain ⟨eqXs,eqArgs,eqProg,eqSs,eqEnvs⟩ := returningSourceGuards_unique values names retCode l1 l2 dest args
      source xs args1 otherXs otherArgs prog otherProg ss otherSs envs otherEnvs guards facts.1
    subst otherXs otherArgs otherProg otherSs otherEnvs
    exact bodyIH

#print axioms selectedReturningHandlerMotive
end InitECandidate.Runtime.WordToStack.ExecutedHandler
