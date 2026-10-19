import InitECandidate.Runtime.WitnessPhysicalRecord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Heap growth and writes to the record's hash/occupancy cells retain its live
continuation data when the concrete slice table is also framed. -/
theorem WitnessPhysicalRecord.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record previous input inputLength frontier nextFrontier : BitVec 64) (persistentFloor : Nat)
    (valid : WitnessPhysicalRecord s record previous input inputLength frontier persistentFloor)
    (growth : frontier.toNat ≤ nextFrontier.toNat)
    (domain : post.memaddrs=s.memaddrs)
    (recordMemory : ∀ offset : Nat, offset<88 → offset≠40 → offset≠80 →
      post.memory (record+BitVec.ofNat 64 offset)=s.memory (record+BitVec.ofNat 64 offset))
    (tableMemory : ∀ watched : BitVec 64, record.toNat+88 ≤ watched.toNat → watched.toNat<frontier.toNat →
      post.memory watched=s.memory watched) :
    WitnessPhysicalRecord post record previous input inputLength nextFrontier persistentFloor := by
  obtain ⟨positive,below,accessible,link,array,count,stage,pointer,length,kind,atStage,atArray,atPointer,
    atLength,tableAbove,tableEnd,table,nibs,branch⟩ := valid
  have field (offset : Nat) (inside : offset<88) (notOcc : offset≠40) (notHash : offset≠80) :=
    recordMemory offset inside notOcc notHash
  have f0 : post.memory record=s.memory record := by simpa using field 0 (by decide) (by decide) (by decide)
  have f8 : post.memory (record+(8 : BitVec 64))=s.memory (record+(8 : BitVec 64)) := by simpa using field 8 (by decide) (by decide) (by decide)
  have f16 : post.memory (record+(16 : BitVec 64))=s.memory (record+(16 : BitVec 64)) := by simpa using field 16 (by decide) (by decide) (by decide)
  have f24 : post.memory (record+(24 : BitVec 64))=s.memory (record+(24 : BitVec 64)) := by simpa using field 24 (by decide) (by decide) (by decide)
  have f32 : post.memory (record+(32 : BitVec 64))=s.memory (record+(32 : BitVec 64)) := by simpa using field 32 (by decide) (by decide) (by decide)
  have f48 : post.memory (record+(48 : BitVec 64))=s.memory (record+(48 : BitVec 64)) := by simpa using field 48 (by decide) (by decide) (by decide)
  have f56 : post.memory (record+(56 : BitVec 64))=s.memory (record+(56 : BitVec 64)) := by simpa using field 56 (by decide) (by decide) (by decide)
  have f64 : post.memory (record+(64 : BitVec 64))=s.memory (record+(64 : BitVec 64)) := by simpa using field 64 (by decide) (by decide) (by decide)
  have f72 : post.memory (record+(72 : BitVec 64))=s.memory (record+(72 : BitVec 64)) := by simpa using field 72 (by decide) (by decide) (by decide)
  refine ⟨positive,below,?_,?_,array,count,stage,pointer,length,kind,?_,?_,?_,?_,tableAbove,
    tableEnd.trans growth,?_,?_,?_⟩
  · intro offset inside; rw [domain]; exact accessible offset inside
  · exact f0.trans link
  · exact f8.trans atStage
  · exact f24.trans atArray
  · exact f48.trans atPointer
  · exact f56.trans atLength
  · exact table.after_memory_between s post array count input inputLength frontier (record.toNat+88)
      tableAbove tableEnd domain (fun watched before above => tableMemory watched above before)
  · intro one
    obtain ⟨n,c,atN,atC⟩ := nibs one
    exact ⟨n,c,f64.trans atN,
      f72.trans atC⟩
  · intro two
    obtain ⟨br,index,atBr,atIndex,indexBound,floorBound,tableBefore,branchEnd,aligned⟩ := branch two
    exact ⟨br,index,f16.trans atBr,
      f32.trans atIndex,
      indexBound,floorBound,tableBefore,branchEnd.trans growth,aligned⟩

#print axioms WitnessPhysicalRecord.after_frame
end InitECandidate.Runtime
