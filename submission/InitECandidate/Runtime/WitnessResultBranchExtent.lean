import InitECandidate.Runtime.WitnessResultAboveStack
import InitECandidate.Runtime.WitnessPhysicalRecordBranchGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The retained-stack frontier bounds the whole parent branch, not only its
slice table. A nonzero delivered child therefore starts beyond that branch. -/
theorem WitnessResultAboveStack.branch_extent {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength top node branch : BitVec 64) (persistentFloor lower : Nat)
    (valid : WitnessResultAboveStack s input inputLength top node persistentFloor lower)
    (nonempty : top≠0) (stage : s.memory (top+8)=.word (2 : BitVec 64))
    (atBranch : s.memory (top+16)=.word branch) :
    node=0 ∨ branch.toNat+176≤node.toNat := by
  rcases valid with zero | ⟨savedFrontier,above,stack⟩
  · exact Or.inl zero
  · have physical := stack.physical s input inputLength savedFrontier top persistentFloor lower
    cases physical with
    | nil => exact False.elim (nonempty rfl)
    | cons recordAbove record ordered tail =>
      obtain ⟨array,index,_,_,_,_,_,_,branchEnd⟩ := record.branch_geometry s top _ input inputLength
        savedFrontier branch persistentFloor stage atBranch
      exact Or.inr (branchEnd.trans above)

#print axioms WitnessResultAboveStack.branch_extent
end InitECandidate.Runtime
