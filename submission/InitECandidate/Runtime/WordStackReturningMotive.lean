import InitECandidate.Runtime.WordStackExecutedSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Assembly
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
def InductionHypothesesFor (price : Compiler.Backend.StackLang.HolProg 64 → Nat) (calleeBudget returnBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) : Prop :=
  (∀ (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (ys : List (WordLocW 64))
    (calleePost popped : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location ys), calleePost) ∧
    ¬ (location ≠ .loc l1 l2 ∨ ys.length ≠ values.length) ∧
    WordSemStateFiniteExact.popEnv calleePost = some popped ∧
    sptDomainEqUnion popped.locals envs.1 envs.2 →
    ExecutedSimulationFor price ac retCode (WordSemStateFiniteExact.setVars values ys popped) returnBudget) ∧
  (∀ (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64)),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    ExecutedSimulationFor price ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))) calleeBudget)


abbrev InductionHypotheses (calleeBudget returnBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) : Prop :=
  InductionHypothesesFor (InitECandidate.Runtime.StackToLab.removalLocalPrice 6
    Compiler.Encoders.RiscV.Target.riscvConfig.addrOffset)
    calleeBudget returnBudget ac values names retCode l1 l2 dest args source

/-- Original semantic auxiliaries may use the already-proved complete
compiler correctness theorem. This does not infer a runtime bound from an
uncosted simulation; quantitative witnesses still come from the executed IHs. -/
theorem InductionHypothesesFor.forget {price : Compiler.Backend.StackLang.HolProg 64 → Nat} {F : Type}
    {calleeBudget returnBudget : Nat} {ac : AsmConfigExact 64}
    {values : List Nat} {names : WordLangCutsetsHOL}
    {retCode : WordLangProgHOL (BitVec 64)} {l1 l2 : Nat} {dest : Option Nat} {args : List Nat}
    {source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F}
    (ih : InductionHypothesesFor price calleeBudget returnBudget ac values names retCode l1 l2 dest args source) :
    Flapjack.WordToStackProofs.CompCorrect.CallReturning.InductionHypotheses
      ac values names retCode l1 l2 dest args source := by
  constructor
  · intro xs args1 prog ss envs location ys calleePost popped facts
    exact Flapjack.WordToStackProofs.CompCorrect.compCorrect ac retCode _
  · intro xs args1 prog ss envs facts
    exact Flapjack.WordToStackProofs.CompCorrect.compCorrect ac prog _

theorem InductionHypotheses.forget {F : Type}
    {calleeBudget returnBudget : Nat} {ac : AsmConfigExact 64}
    {values : List Nat} {names : WordLangCutsetsHOL}
    {retCode : WordLangProgHOL (BitVec 64)} {l1 l2 : Nat} {dest : Option Nat} {args : List Nat}
    {source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F}
    (ih : InductionHypotheses calleeBudget returnBudget ac values names retCode l1 l2 dest args source) :
    Flapjack.WordToStackProofs.CompCorrect.CallReturning.InductionHypotheses
      ac values names retCode l1 l2 dest args source := InductionHypothesesFor.forget ih

#print axioms InductionHypothesesFor.forget
end InitECandidate.Runtime.WordToStack.ExecutedReturning
