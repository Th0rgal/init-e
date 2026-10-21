import InitECandidate.Runtime.WordStackReturningSelectedMotive
import InitECandidate.Runtime.WordStackReturningNone
import InitECandidate.Runtime.WordExecutionReturningCost
import InitECandidate.Runtime.WordStackReturningMotive
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- Actual source-call facts specialize dynamic-cost induction hypotheses to
fixed callee and continuation budgets without charging an unexecuted branch. -/
theorem executedSimulation_returningNone_selected {F : Type}
    (targetPrice : StackLang.HolProg 64 → Nat)
    [StackToLab.ConservativeRemovalPrice targetPrice]
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (ac : AsmConfigExact 64)
    (values : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (bodyResult : Option (WordSemResult 64))
    (bodyPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (bodyRun : evaluate prog (callEnv args1 ss (pushEnv envs none (decClock source))) =
      (bodyResult,bodyPost))
    (nonzero : source.clock ≠ 0)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (localBound : 63+39*(args.length+1-22)+21*(values.length+1-22) ≤
      factor * price (.call (some (values,names,retCode,l1,l2)) dest args none) source)
    (bodyIH : ExecutedSimulationFor targetPrice ac prog
      (callEnv args1 ss (pushEnv envs none (decClock source)))
      (factor * wordExecutionCost price prog (callEnv args1 ss (pushEnv envs none (decClock source)))))
    (returnIH : ∀ location returned post popped,
      evaluate prog (callEnv args1 ss (pushEnv envs none (decClock source))) =
        (some (.result location returned),post) →
      ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) →
      popEnv post = some popped → sptDomainEqUnion popped.locals envs.1 envs.2 →
      ExecutedSimulationFor targetPrice ac retCode (setVars values returned popped)
        (factor * wordExecutionCost price retCode (setVars values returned popped))) :
    ExecutedSimulationFor targetPrice ac
      (.call (some (values,names,retCode,l1,l2)) dest args none) source
      (factor * wordExecutionCost price
        (.call (some (values,names,retCode,l1,l2)) dest args none) source) := by
  have motive := selectedReturningNoneMotive targetPrice price factor ac values names retCode
    l1 l2 dest args source xs args1 prog ss envs guards bodyResult bodyPost bodyRun bodyIH returnIH
  have simulation := executedSimulation_returningNone (price := targetPrice)
    (factor * wordExecutionCost price prog (callEnv args1 ss (pushEnv envs none (decClock source))))
    (factor * wordReturningContinuationCost price values retCode l1 l2 none envs bodyResult bodyPost)
    ac values names retCode l1 l2 dest args source covered motive
  apply simulation.mono
  rw [wordExecutionCost_returning price values names retCode l1 l2 dest args none source
    xs args1 prog ss envs guards nonzero bodyResult bodyPost bodyRun]
  simp only [Nat.mul_add]
  omega

#print axioms executedSimulation_returningNone_selected
end InitECandidate.Runtime.WordToStack.ExecutedReturning
