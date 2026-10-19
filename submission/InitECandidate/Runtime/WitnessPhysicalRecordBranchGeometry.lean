import InitECandidate.Runtime.WitnessPhysicalRecord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem WitnessPhysicalRecord.branch_geometry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record previous input inputLength frontier branch : BitVec 64) (persistentFloor : Nat)
    (valid : WitnessPhysicalRecord s record previous input inputLength frontier persistentFloor)
    (stage : s.memory (record+8)=.word (2 : BitVec 64)) (cell : s.memory (record+16)=.word branch) :
    ∃ array index : BitVec 64, s.memory (record+24)=.word array ∧ s.memory (record+32)=.word index ∧
      index.toNat<16 ∧ record.toNat+88≤array.toNat ∧ array.toNat+272≤branch.toNat ∧
      persistentFloor≤branch.toNat ∧ branch.toNat+176≤frontier.toNat := by
  obtain ⟨positive,below,accessible,link,array,count,kind,p,n,arity,atKind,atArray,atP,atN,tableAbove,
    tableEnd,table,nibs,branches⟩ := valid
  have sameKind : kind=2 := HolWordLab.word.inj (atKind.symm.trans stage)
  subst kind
  obtain ⟨actual,index,atBranch,atIndex,indexBound,floorBound,tableBefore,branchEnd,aligned⟩ := branches rfl
  have sameBranch : actual=branch := HolWordLab.word.inj (atBranch.symm.trans cell)
  subst actual
  exact ⟨array,index,atArray,atIndex,indexBound,tableAbove,tableBefore,floorBound,branchEnd⟩

#print axioms WitnessPhysicalRecord.branch_geometry
end InitECandidate.Runtime
