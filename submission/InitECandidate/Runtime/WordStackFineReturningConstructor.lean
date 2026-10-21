import InitECandidate.Runtime.WordStackFineReturningNone
import InitECandidate.Runtime.WordStackFineReturningZero
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- Complete returning-call constructor for dynamic source execution costs.
The recursive premises mention only actually reached source states. -/
theorem executedSimulation_returningNone_fine {F : Type}
    (targetPrice : StackLang.HolProg 64 → Nat)
    [StackToLab.ConservativeRemovalPrice targetPrice]
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (ac : AsmConfigExact 64)
    (values : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (localBound : 63+39*(args.length+1-22)+21*(values.length+1-22) ≤
      factor * price (.call (some (values,names,retCode,l1,l2)) dest args none) source)
    (calleeIH : ∀ xs args1 prog ss envs,
      SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs →
      source.clock ≠ 0 →
      ExecutedSimulationFor targetPrice ac prog
        (callEnv args1 ss (pushEnv envs none (decClock source)))
        (factor * wordExecutionCost price prog (callEnv args1 ss (pushEnv envs none (decClock source)))))
    (returnIH : ∀ xs args1 prog ss envs location returned post popped,
      SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs →
      source.clock ≠ 0 →
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
  classical
  by_cases valid : ∃ xs args1 prog ss envs,
      SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs
  · obtain ⟨xs,args1,prog,ss,envs,guards⟩ := valid
    by_cases zero : source.clock = 0
    · exact executedSimulation_returningNone_zero (targetPrice := targetPrice) price factor ac values names
        retCode l1 l2 dest args source xs args1 prog ss envs guards zero covered localBound
    · rcases bodyRun : evaluate prog (callEnv args1 ss (pushEnv envs none (decClock source))) with
        ⟨bodyResult,bodyPost⟩
      exact ExecutedReturning.executedSimulation_returningNone_selected targetPrice price factor ac
        values names retCode l1 l2 dest args source xs args1 prog ss envs guards bodyResult bodyPost bodyRun
        zero covered localBound (calleeIH xs args1 prog ss envs guards zero)
        (returnIH xs args1 prog ss envs · · · · guards zero)
  · intro k f frame sourcePost target result bs finalBs n finalIndex compiled lens facts small
    obtain ⟨xs,args1,prog,ss,envs,guards⟩ := sourceGuardsOfNotError values names retCode l1 l2
      dest args source sourcePost result facts.1 facts.2.1
    exact False.elim (valid ⟨xs,args1,prog,ss,envs,guards⟩)

#print axioms executedSimulation_returningNone_fine
end InitECandidate.Runtime.WordToStack
