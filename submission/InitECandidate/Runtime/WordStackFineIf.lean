import InitECandidate.Runtime.WordStackFineControlPrice
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.FineCost

theorem executedSimulation_ite {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec 64)) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (localBound : 30 ≤ factor * price (.ite comparison register operand first second) source)
    (firstIH : ∀ x y,
      WordSemStateFiniteExact.getVar register source = some x →
      WordSemStateFiniteExact.getVarImm operand source = some y →
      wordSemWordCmp comparison x y = some true →
      ExecutedSimulation ac first source (factor * wordExecutionCost price first source))
    (secondIH : ∀ x y,
      WordSemStateFiniteExact.getVar register source = some x →
      WordSemStateFiniteExact.getVarImm operand source = some y →
      wordSemWordCmp comparison x y = some false →
      ExecutedSimulation ac second source (factor * wordExecutionCost price second source)) :
    ExecutedSimulation ac (.ite comparison register operand first second) source
      (factor * wordExecutionCost price (.ite comparison register operand first second) source) := by
  exact executedSimulation_iteWithPrice
    (StackToLab.removalLocalPrice 6 riscvConfig.addrOffset) 7 12 11 30 StackToLab.conservativeConditionPriceCaps ac price factor comparison register operand first second source localBound firstIH secondIH

#print axioms executedSimulation_ite
end InitECandidate.Runtime.WordToStack
