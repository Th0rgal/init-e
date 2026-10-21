import InitECandidate.Runtime.WordStackFineControlPrice
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.FineCost

theorem executedSimulation_seq {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (free : price (.seq first second) source = 0)
    (firstIH : ExecutedSimulation ac first source (factor * wordExecutionCost price first source))
    (secondIH : ∀ middle, WordSemStateFiniteExact.evaluate first source = (none, middle) →
      ExecutedSimulation ac second middle (factor * wordExecutionCost price second middle)) :
    ExecutedSimulation ac (.seq first second) source
      (factor * wordExecutionCost price (.seq first second) source) := by
  exact executedSimulation_seqWithPrice
    (StackToLab.removalLocalPrice 6 riscvConfig.addrOffset) (fun _ _ => rfl) ac price factor first second source free firstIH secondIH

#print axioms executedSimulation_seq
end InitECandidate.Runtime.WordToStack
