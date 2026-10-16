import InitECandidate.Runtime.WordWork
import InitECandidate.Runtime.WordToStackLeafBudget

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Encoders.Asm

theorem leafBudget_le_wordWork {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    leafBudget p ≤ wordWork p source := by
  have small : leafBudget p ≤ 1 := by cases p <;> simp [leafBudget]
  exact Nat.le_trans small (one_le_wordWork p source)

/-- Every nonrecursive constructor is now funded by the total source-state
budget, retaining the complete compiler simulation statement. -/
theorem wordWork_leaf_correct {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (leaf : leafCase p = true) :
    BoundedSimulation ac p source (wordWork p source) :=
  (leafCase_correct ac p source leaf).mono (leafBudget_le_wordWork p source)

#print axioms wordWork_leaf_correct
end InitECandidate.Runtime.WordToStack
