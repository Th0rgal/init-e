import InitECandidate.Runtime.WordStackRegisteredSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
def InductionHypotheses (price : HolProg 64 → Nat) (calleeBudget returnBudget handlerBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) : Prop :=
  (∀ (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (ys : List (WordLocW 64))
    (calleePost popped : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location ys), calleePost) ∧
    ¬ (location ≠ .loc l1 l2 ∨ ys.length ≠ values.length) ∧
    WordSemStateFiniteExact.popEnv calleePost = some popped ∧
    sptDomainEqUnion popped.locals envs.1 envs.2 →
    ExecutedSimulationFor price ac retCode (WordSemStateFiniteExact.setVars values ys popped) returnBudget) ∧
  (∀ (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location value : WordLocW 64)
    (calleePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),calleePost) ∧
    ¬ location ≠ .loc h1 h2 ∧
    sptDomainEqUnion calleePost.locals envs.1 envs.2 →
    ExecutedSimulationFor price ac handlerCode (WordSemStateFiniteExact.setVar handlerVar value calleePost) handlerBudget) ∧
  (∀ (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64)),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    ExecutedSimulationFor price ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) calleeBudget)

theorem InductionHypotheses.forget {price : HolProg 64 → Nat}
    {calleeBudget returnBudget handlerBudget : Nat} {F : Type} {ac : AsmConfigExact 64}
    {values : List Nat} {names : WordLangCutsetsHOL} {retCode : WordLangProgHOL (BitVec 64)}
    {l1 l2 : Nat} {dest : Option Nat} {args : List Nat}
    {handlerVar h1 h2 : Nat} {handlerCode : WordLangProgHOL (BitVec 64)}
    {source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F}
    (ih : InductionHypotheses price calleeBudget returnBudget handlerBudget ac values names retCode l1 l2
      dest args handlerVar h1 h2 handlerCode source) :
    Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler.InductionHypotheses ac values names retCode l1 l2
      dest args handlerVar h1 h2 handlerCode source := by
  refine ⟨?_,?_,?_⟩
  · intro xs args1 prog ss envs location ys calleePost popped facts
    exact Flapjack.WordToStackProofs.CompCorrect.compCorrect ac retCode _
  · intro xs args1 prog ss envs location value calleePost facts
    exact Flapjack.WordToStackProofs.CompCorrect.compCorrect ac handlerCode _
  · intro xs args1 prog ss envs facts
    exact Flapjack.WordToStackProofs.CompCorrect.compCorrect ac prog _

#print axioms InductionHypotheses.forget
end InitECandidate.Runtime.WordToStack.ExecutedHandler
