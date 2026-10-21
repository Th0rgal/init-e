import InitECandidate.Runtime.WordStackRefinedSimulation
import InitECandidate.Runtime.WordStackExecutedSeq
import InitECandidate.Runtime.WordStackExecutedIf
import InitECandidate.Runtime.WordStackExecutedLoop
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.StackToLab

/-- Two spill loads or one spill plus constant materialization, followed by
one comparison. Encoding and padding share their instruction spans. -/
def refinedConditionPriceCaps :
    ConditionPriceCaps (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) 6 6 11 23 where
  freeSeq := fun _ _ => rfl
  load := fun r o h => by simp only [guest_spill_load_refined_price r o h]; exact Nat.le_refl _
  constant := fun r v => by
    have bound := const_native_length_le r v
    simpa only [refinedRemovalLocalPrice, refinedNativePriceWithGap, instLocalCost,
      max_le_iff, Nat.le_refl, and_true] using bound
  branch := fun _ _ _ _ _ => rfl
  twoLoads := by decide
  loadConstant := by decide

theorem refinedExecutedSimulation_if {F : Type} (budget : Nat)
    (ac : AsmConfigExact 64) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ih : ExecutedIf.OriginalInductionHypothesesFor
      (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) budget ac comparison register operand first second source) :
    RefinedExecutedSimulation ac (.ite comparison register operand first second) source (budget + 23) :=
  ExecutedIf.compCorrectIfWithPrice _ 6 6 11 23 refinedConditionPriceCaps
    budget ac comparison register operand first second source ih

theorem refinedExecutedSimulation_seq {F : Type} (firstBudget secondBudget : Nat)
    (ac : AsmConfigExact 64) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        RefinedExecutedSimulation ac second middle secondBudget) ∧ RefinedExecutedSimulation ac first source firstBudget) :
    RefinedExecutedSimulation ac (.seq first second) source (firstBudget + secondBudget) :=
  ExecutedSeq.compCorrectSeqWithPrice _ (fun _ _ => rfl)
    firstBudget secondBudget ac first second source ih

theorem refinedExecutedSimulation_loop {F : Type} (bodyBudget recursiveBudget : Nat)
    (ac : AsmConfigExact 64) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ih : ExecutedLoop.InductionHypothesesFor (refinedRemovalLocalPrice 6 riscvConfig.addrOffset)
      bodyBudget recursiveBudget ac names exitNames body source) :
    RefinedExecutedSimulation ac (.loop names body exitNames) source (2 + bodyBudget + recursiveBudget) :=
  ExecutedLoop.compCorrectLoopWithPrice _ (fun _ => rfl)
    bodyBudget recursiveBudget ac names exitNames body source ih

#print axioms refinedConditionPriceCaps
#print axioms refinedExecutedSimulation_if
#print axioms refinedExecutedSimulation_seq
#print axioms refinedExecutedSimulation_loop
end InitECandidate.Runtime.WordToStack
