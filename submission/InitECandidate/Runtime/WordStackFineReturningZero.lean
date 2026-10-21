import InitECandidate.Runtime.WordExecutionReturningZero
import InitECandidate.Runtime.WordStackReturningNone
import InitECandidate.Runtime.WordStackReturningHandler
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open InitECandidate.Runtime.FineCost
variable {targetPrice : StackLang.HolProg 64 → Nat} [StackToLab.ConservativeRemovalPrice targetPrice]

/-- A clock-exhausted call has vacuous recursive hypotheses and pays only
its local compiler bound, retaining earlier target resource exits. -/
theorem executedSimulation_returningNone_zero {F : Type}
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (ac : AsmConfigExact 64)
    (values : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (zero : source.clock = 0)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (localBound : 63+39*(args.length+1-22)+21*(values.length+1-22) ≤
      factor * price (.call (some (values,names,retCode,l1,l2)) dest args none) source) :
    ExecutedSimulationFor targetPrice ac (.call (some (values,names,retCode,l1,l2)) dest args none) source
      (factor * wordExecutionCost price (.call (some (values,names,retCode,l1,l2)) dest args none) source) := by
  have ih : ExecutedReturning.InductionHypothesesFor targetPrice 0 0 ac values names retCode l1 l2 dest args source := by
    constructor
    · intro xs args1 prog ss envs location returned post popped facts
      exact False.elim (facts.2.1 zero)
    · intro xs args1 prog ss envs facts
      exact False.elim (facts.2 zero)
  have simulation := ExecutedReturning.executedSimulation_returningNone (price := targetPrice)
    0 0 ac values names retCode l1 l2 dest args source covered ih
  apply simulation.mono
  rw [wordExecutionCost_returning_zero price values names retCode l1 l2 dest args none source
    xs args1 prog ss envs guards zero]
  simpa only [Nat.zero_add] using localBound

/-- A clock-exhausted call has vacuous recursive hypotheses and pays only
its local compiler bound, retaining earlier target resource exits. -/
theorem executedSimulation_returningHandler_zero {F : Type}
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
    (zero : source.clock = 0)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (localBound : 189+39*(args.length+1-22)+21*(values.length+1-22) ≤
      factor * price (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source) :
    ExecutedSimulationFor targetPrice ac (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source
      (factor * wordExecutionCost price (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source) := by
  have ih : ExecutedHandler.InductionHypotheses targetPrice 0 0 0 ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source := by
    refine ⟨?_,?_,?_⟩
    · intro xs args1 prog ss envs location returned post popped facts
      exact False.elim (facts.2.1 zero)
    · intro xs args1 prog ss envs location value post facts
      exact False.elim (facts.2.1 zero)
    · intro xs args1 prog ss envs facts
      exact False.elim (facts.2 zero)
  have simulation := ExecutedHandler.executedSimulation_returningHandler (price := targetPrice)
    0 0 0 ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source covered ih
  apply simulation.mono
  rw [wordExecutionCost_returning_zero price values names retCode l1 l2 dest args (some (handlerVar,handlerCode,h1,h2)) source
    xs args1 prog ss envs guards zero]
  simpa only [Nat.zero_add,Nat.max_self] using localBound

#print axioms executedSimulation_returningNone_zero
#print axioms executedSimulation_returningHandler_zero
end InitECandidate.Runtime.WordToStack
