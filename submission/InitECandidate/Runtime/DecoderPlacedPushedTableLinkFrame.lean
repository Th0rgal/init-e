import InitECandidate.Runtime.DecodeBranchPlacement
import InitECandidate.Runtime.DecoderPushedTableLinkFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem DecoderPlacedPushedTable.after_link {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength : BitVec 64) (ceiling floor : Nat)
    (valid : DecoderPlacedPushedTable s record pointer length input inputLength ceiling floor)
    (recordBelow : record.toNat < ceiling)
    (globals : post.globals=s.globals) (domain : post.memaddrs=s.memaddrs)
    (memory : ∀ watched : BitVec 64, watched ≠ record → post.memory watched=s.memory watched) :
    DecoderPlacedPushedTable post record pointer length input inputLength ceiling floor := by
  refine ⟨valid.1.after_link s post record pointer length input inputLength ceiling recordBelow globals domain memory,?_⟩
  intro stage
  have fieldMemory (offset : BitVec 64) (positive : offset ≠ 0) :
      post.memory (record+offset)=s.memory (record+offset) := by
    apply memory
    intro same
    have equal : record+offset=record+0 := by simpa using same
    have zero : offset=0 := by simpa using equal
    exact positive zero
  have beforeStage : s.memory (record+8)=.word (2 : BitVec 64) := (fieldMemory 8 (by decide)).symm.trans stage
  obtain ⟨array,branch,heap,atArray,atBranch,floorBound,tableEnd,branchEnd,aligned,atHeap,capped⟩ := valid.2 beforeStage
  exact ⟨array,branch,heap,(fieldMemory 24 (by decide)).trans atArray,(fieldMemory 16 (by decide)).trans atBranch,
    floorBound,tableEnd,branchEnd,aligned,by rw [globals]; exact atHeap,capped⟩

#print axioms DecoderPlacedPushedTable.after_link
end InitECandidate.Runtime
