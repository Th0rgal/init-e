import InitECandidate.Runtime.WitnessPhysicalRecordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Advancing a branch index retains the live record when its stable fields
and real slice table below the branch constructor are framed. -/
theorem WitnessPhysicalRecord.after_branch_index {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record previous input inputLength frontier nextFrontier branch nextIndex : BitVec 64) (persistentFloor : Nat)
    (valid : WitnessPhysicalRecord s record previous input inputLength frontier persistentFloor)
    (stageCell : s.memory (record+8)=.word (2 : BitVec 64))
    (branchCell : s.memory (record+16)=.word branch)
    (growth : frontier.toNat≤nextFrontier.toNat) (domain : post.memaddrs=s.memaddrs)
    (indexBound : nextIndex.toNat<16) (indexCell : post.memory (record+32)=.word nextIndex)
    (recordMemory : ∀ offset : Nat, offset<88 → offset≠32 → offset≠40 → offset≠80 →
      post.memory (record+BitVec.ofNat 64 offset)=s.memory (record+BitVec.ofNat 64 offset))
    (tableMemory : ∀ watched : BitVec 64, record.toNat+88≤watched.toNat → watched.toNat<branch.toNat →
      post.memory watched=s.memory watched) :
    WitnessPhysicalRecord post record previous input inputLength nextFrontier persistentFloor := by
  obtain ⟨positive,below,accessible,link,array,count,stage,pointer,length,kind,atStage,atArray,atPointer,
    atLength,tableAbove,tableEnd,table,nibs,branchData⟩ := valid
  have sameStage : stage=2 := HolWordLab.word.inj (atStage.symm.trans stageCell)
  subst stage
  have countEq : count=17 := by
    rcases kind with ⟨impossible,_⟩ | ⟨_,same⟩
    · cases impossible
    · exact same
  subst count
  obtain ⟨br,index,atBr,atIndex,oldIndexBound,floorBound,tableBefore,branchEnd,aligned⟩ := branchData rfl
  have sameBranch : br=branch := HolWordLab.word.inj (atBr.symm.trans branchCell)
  subst br
  have field (offset : Nat) (inside : offset<88) (notIndex : offset≠32) (notOcc : offset≠40) (notHash : offset≠80) :=
    recordMemory offset inside notIndex notOcc notHash
  have f0 : post.memory record=s.memory record := by simpa using field 0 (by decide) (by decide) (by decide) (by decide)
  have f8 : post.memory (record+(8 : BitVec 64))=s.memory (record+(8 : BitVec 64)) := by simpa using field 8 (by decide) (by decide) (by decide) (by decide)
  have f16 : post.memory (record+(16 : BitVec 64))=s.memory (record+(16 : BitVec 64)) := by simpa using field 16 (by decide) (by decide) (by decide) (by decide)
  have f24 : post.memory (record+(24 : BitVec 64))=s.memory (record+(24 : BitVec 64)) := by simpa using field 24 (by decide) (by decide) (by decide) (by decide)
  have f48 : post.memory (record+(48 : BitVec 64))=s.memory (record+(48 : BitVec 64)) := by simpa using field 48 (by decide) (by decide) (by decide) (by decide)
  have f56 : post.memory (record+(56 : BitVec 64))=s.memory (record+(56 : BitVec 64)) := by simpa using field 56 (by decide) (by decide) (by decide) (by decide)

  refine ⟨positive,below,?_,f0.trans link,array,17,2,pointer,length,Or.inr ⟨rfl,rfl⟩,f8.trans atStage,
    f24.trans atArray,f48.trans atPointer,f56.trans atLength,tableAbove,tableEnd.trans growth,?_,?_,?_⟩
  · intro offset inside; rw [domain]; exact accessible offset inside
  · exact table.after_memory_between s post array 17 input inputLength branch (record.toNat+88)
      tableAbove (by simpa using tableBefore) domain (fun watched hi lo => tableMemory watched lo hi)
  · intro impossible; cases impossible
  · intro _
    exact ⟨branch,nextIndex,f16.trans branchCell,indexCell,indexBound,floorBound,tableBefore,branchEnd.trans growth,aligned⟩

#print axioms WitnessPhysicalRecord.after_branch_index
end InitECandidate.Runtime
