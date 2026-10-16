import InitECandidate.Runtime.WordToStackBudget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler
namespace InitECandidate.Runtime.WordToStack.CallReturningHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
def InductionHypotheses (calleeBudget returnBudget handlerBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (ys : List (WordLocW width))
    (calleePost popped : WordSemStateFiniteExact width (Nat × C) F),
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
    BoundedSimulation ac retCode (WordSemStateFiniteExact.setVars values ys popped) returnBudget) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location value : WordLocW width)
    (calleePost : WordSemStateFiniteExact width (Nat × C) F),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),calleePost) ∧
    ¬ location ≠ .loc h1 h2 ∧
    sptDomainEqUnion calleePost.locals envs.1 envs.2 →
    BoundedSimulation ac handlerCode (WordSemStateFiniteExact.setVar handlerVar value calleePost) handlerBudget) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    BoundedSimulation ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) calleeBudget)


theorem InductionHypotheses.forget {width : Nat} [NeZero width] {C F : Type}
    {calleeBudget returnBudget handlerBudget : Nat} {ac : AsmConfigExact width}
    {values : List Nat} {names : WordLangCutsetsHOL} {retCode : WordLangProgHOL (BitVec width)}
    {l1 l2 : Nat} {dest : Option Nat} {args : List Nat} {handlerVar h1 h2 : Nat}
    {handlerCode : WordLangProgHOL (BitVec width)}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    (ih : InductionHypotheses calleeBudget returnBudget handlerBudget ac values names retCode
      l1 l2 dest args handlerVar h1 h2 handlerCode source) :
    Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler.InductionHypotheses
      ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source := by
  refine ⟨?_, ?_, ?_⟩
  · intro xs args1 prog ss envs location ys calleePost popped facts
    exact (ih.1 xs args1 prog ss envs location ys calleePost popped facts).forget
  · intro xs args1 prog ss envs location value calleePost facts
    exact (ih.2.1 xs args1 prog ss envs location value calleePost facts).forget
  · intro xs args1 prog ss envs facts
    exact (ih.2.2 xs args1 prog ss envs facts).forget

#print axioms InductionHypotheses.forget

end InitECandidate.Runtime.WordToStack.CallReturningHandler
