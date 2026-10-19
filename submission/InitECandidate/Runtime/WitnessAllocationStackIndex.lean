import InitECandidate.Runtime.WitnessPhysicalRecordIndex
import InitECandidate.Runtime.WitnessAllocationStackHashFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Current branch-index writes are below every saved parent; branch child
stores are above its table and its saved parent allocation frontier. -/
theorem WitnessAllocationStack.after_branch_index {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier nextFrontier top branch nextIndex : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (nonempty : top≠0) (stage : s.memory (top+8)=.word (2 : BitVec 64))
    (atBranch : s.memory (top+16)=.word branch)
    (growth : frontier.toNat≤nextFrontier.toNat) (domain : post.memaddrs=s.memaddrs)
    (indexBound : nextIndex.toNat<16) (indexCell : post.memory (top+32)=.word nextIndex)
    (recordMemory : ∀ offset : Nat, offset<88 → offset≠32 → offset≠40 → offset≠80 →
      post.memory (top+BitVec.ofNat 64 offset)=s.memory (top+BitVec.ofNat 64 offset))
    (upperMemory : ∀ watched : BitVec 64, top.toNat+88≤watched.toNat → watched.toNat<branch.toNat →
      post.memory watched=s.memory watched) :
    WitnessAllocationStack post input inputLength nextFrontier persistentFloor lower top := by
  cases stack with
  | nil => exact False.elim (nonempty rfl)
  | cons parent above valid floorBound parentBound ordered branchAbove tail =>
    have current := valid.after_branch_index s post top _ input inputLength frontier nextFrontier branch nextIndex persistentFloor
      stage atBranch growth domain indexBound indexCell recordMemory upperMemory
    obtain ⟨actual,cell,parentBeforeBranch⟩ := branchAbove stage
    have same := HolWordLab.word.inj (cell.symm.trans atBranch)
    subst actual
    have older := tail.rebase s input inputLength parent _ persistentFloor lower (top.toNat+88) ordered
    have olderPost := older.after_frame s post input inputLength parent _ persistentFloor (top.toNat+88) domain
      parent lower (Nat.le_refl _) (by omega) (by
        intro watched lo hi
        exact upperMemory watched lo (hi.trans_le parentBeforeBranch))
    refine .cons parent above current floorBound (parentBound.trans growth) ordered ?_ olderPost
    intro _
    have branchFrame : post.memory (top+16)=s.memory (top+16) := by
      simpa using recordMemory 16 (by decide) (by decide) (by decide) (by decide)
    exact ⟨branch,branchFrame.trans atBranch,parentBeforeBranch⟩

#print axioms WitnessAllocationStack.after_branch_index
end InitECandidate.Runtime
