import InitECandidate.Runtime.StackRemovalLeafSimulation
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Local compiler obligations: proved leaf transfers and constructor-local
control prices. No recursive execution or desired whole-run budget is assumed. -/
structure RemovalPriceCaps {F : Type} (sourcePrice targetPrice : HolProg 64 → Nat)
    (bounds : BitVec 64 × BitVec 64) : Prop where
  leaf : ∀ p (source : StackSemStateFiniteExact 64 LabToTarget.Config F),
    removalSupported p = true → removalLeaf p = true →
    RemovalCostSimulationFor sourcePrice targetPrice false bounds p source
  freeSeq : ∀ first second, targetPrice (.seq first second) = 0
  branch : ∀ cmp reg operand yes no left right,
    targetPrice (.ite cmp reg operand left right) ≤ sourcePrice (.ite cmp reg operand yes no)
  loopNode : ∀ body targetBody, targetPrice (.loop targetBody) ≤ sourcePrice (.loop body)
  tail : ∀ dest handler, targetPrice (.call none dest none) ≤ sourcePrice (.call none dest handler)
  raw : ∀ label, targetPrice (.rawCall label) ≤ sourcePrice (.rawCall label)
  returning : ∀ body link l1 l2 dest handler targetBody targetHandler,
    targetPrice (.call (some (targetBody,link,l1,l2)) dest targetHandler) ≤
    sourcePrice (.call (some (body,link,l1,l2)) dest handler)

/-- The existing conservative table supplies the same local interface. -/
def conservativeRemovalPriceCaps {F : Type} (gap : Nat) (bounds : BitVec 64 × BitVec 64) :
    RemovalPriceCaps (F := F) (removalLocalPrice gap bounds) (nativePriceWithGap gap) bounds where
  leaf := fun p source supported leaf => removalCostSimulation_leaf gap bounds p source supported leaf
  freeSeq := fun _ _ => rfl
  branch := fun _ _ _ _ _ _ _ => Nat.le_refl _
  loopNode := fun _ _ => Nat.le_refl _
  tail := fun _ _ => Nat.le_refl _
  raw := fun _ => Nat.le_refl _
  returning := fun _ _ _ _ _ _ _ _ => Nat.le_refl _

#print axioms conservativeRemovalPriceCaps
end InitECandidate.Runtime.StackToLab
