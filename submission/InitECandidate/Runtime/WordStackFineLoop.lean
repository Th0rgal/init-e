import InitECandidate.Runtime.WordStackFineControlPrice
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.FineCost

theorem executedSimulation_loop {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (localBound : 2 ≤ factor * price (.loop names body exitNames) source)
    (bodyIH : ∀ cutSource, WordSemStateFiniteExact.cutState (names, .ln) source = some cutSource →
      ExecutedSimulation ac body cutSource (factor * wordExecutionCost price body cutSource))
    (recursiveIH : ∀ cutSource bodyResult bodyPost,
      WordSemStateFiniteExact.cutState (names, .ln) source = some cutSource →
      WordSemStateFiniteExact.evaluate body cutSource = (bodyResult, bodyPost) →
      wordSemContLoop bodyResult = true → bodyPost.clock ≠ 0 →
      ExecutedSimulation ac (wordSemSTOP (.loop names body exitNames))
        (WordSemStateFiniteExact.decClock bodyPost)
        (factor * wordExecutionCost price (wordSemSTOP (.loop names body exitNames))
          (WordSemStateFiniteExact.decClock bodyPost))) :
    ExecutedSimulation ac (.loop names body exitNames) source
      (factor * wordExecutionCost price (.loop names body exitNames) source) := by
  exact executedSimulation_loopWithPrice
    (StackToLab.removalLocalPrice 6 riscvConfig.addrOffset) (fun _ => rfl) ac price factor names exitNames body source localBound bodyIH recursiveIH

#print axioms executedSimulation_loop
end InitECandidate.Runtime.WordToStack
