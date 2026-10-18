import InitECandidate.Runtime.WordPathWork
import InitECandidate.Runtime.WordToStackLeafBudget

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Encoders.Asm

theorem leafBudget_le_wordPathWork {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    leafBudget p ≤ wordPathWork p source := by
  have small : leafBudget p ≤ 1 := by cases p <;> simp [leafBudget]
  exact Nat.le_trans small (one_le_wordPathWork p source)

/-- Every nonrecursive constructor is now funded by the total source-state
budget, retaining the complete compiler simulation statement. -/
theorem wordPathWork_leaf_correct {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (leaf : leafCase p = true) :
    BoundedSimulation ac p source (wordPathWork p source) :=
  (leafCase_correct ac p source leaf).mono (leafBudget_le_wordPathWork p source)

#print axioms wordPathWork_leaf_correct
end InitECandidate.Runtime.WordToStack
