import InitECandidate.Runtime.WordToStackBudget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning
namespace InitECandidate.Runtime.WordToStack.CallReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
def InductionHypotheses (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (ys : List (WordLocW width))
    (calleePost popped : WordSemStateFiniteExact width (Nat × C) F),
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
    BoundedSimulation ac retCode (WordSemStateFiniteExact.setVars values ys popped) returnBudget) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    BoundedSimulation ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))) calleeBudget)


theorem InductionHypotheses.forget {width : Nat} [NeZero width] {C F : Type}
    {calleeBudget returnBudget : Nat} {ac : AsmConfigExact width}
    {values : List Nat} {names : WordLangCutsetsHOL}
    {retCode : WordLangProgHOL (BitVec width)} {l1 l2 : Nat} {dest : Option Nat} {args : List Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    (ih : InductionHypotheses calleeBudget returnBudget ac values names retCode l1 l2 dest args source) :
    Flapjack.WordToStackProofs.CompCorrect.CallReturning.InductionHypotheses
      ac values names retCode l1 l2 dest args source := by
  constructor
  · intro xs args1 prog ss envs location ys calleePost popped facts
    exact (ih.1 xs args1 prog ss envs location ys calleePost popped facts).forget
  · intro xs args1 prog ss envs facts
    exact (ih.2 xs args1 prog ss envs facts).forget


end InitECandidate.Runtime.WordToStack.CallReturning
