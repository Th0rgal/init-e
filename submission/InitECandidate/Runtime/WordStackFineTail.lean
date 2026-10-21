import InitECandidate.Runtime.WordStackFineTailPrice
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.FineCost
theorem executedSimulation_tailCall {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (localBound : 41 ≤ factor * price (.call none dest args handler) source)
    (ih : ∀ (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat),
      WordSemStateFiniteExact.getVars args source = some xs ∧
      ¬ wordSemBadDestArgs dest args = true ∧
      wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat)) xs)
        source.code source.stackSize = some (args1, prog, ss) ∧
      handler = none ∧ source.clock ≠ 0 →
      ExecutedSimulation ac prog
        (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source))
        (factor * wordExecutionCost price prog
          (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)))) :
    ExecutedSimulation ac (.call none dest args handler) source
      (factor * wordExecutionCost price (.call none dest args handler) source) := by
  exact executedSimulation_tailCallWithPrice
    (StackToLab.removalLocalPrice 6 riscvConfig.addrOffset) ac price factor dest args handler source
    covered localBound ih

#print axioms executedSimulation_tailCall
end InitECandidate.Runtime.WordToStack
