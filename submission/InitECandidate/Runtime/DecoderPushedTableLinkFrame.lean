import InitECandidate.Runtime.DecodeStepPendingTableMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

private theorem record_offset_separate (record : BitVec 64) (offset : BitVec 64) (nonzero : offset ≠ 0) :
    record+offset ≠ record := by
  intro same
  have zero : offset=0 := by
    have equal : record+offset = record+0 := by simpa using same
    simpa using equal
  exact nonzero zero

theorem DecoderPushedTable.after_link {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength : BitVec 64) (ceiling : Nat)
    (valid : DecoderPushedTable s record pointer length input inputLength ceiling)
    (recordBelow : record.toNat < ceiling)
    (globals : post.globals=s.globals) (domain : post.memaddrs=s.memaddrs)
    (memory : ∀ watched : BitVec 64, watched ≠ record → post.memory watched=s.memory watched) :
    DecoderPushedTable post record pointer length input inputLength ceiling := by
  obtain ⟨array,count,stage,heap,kind,fields,table,above,extent,heapGlobal,capped,aligned⟩ := valid
  obtain ⟨atStage,atArray,atPointer,atLength,extension,branch⟩ := fields
  have fieldMemory (offset : BitVec 64) (positive : offset ≠ 0) :
      post.memory (record+offset)=s.memory (record+offset) :=
    memory _ (record_offset_separate record offset positive)
  have fieldsPost : DecoderRecordFields post record array pointer length stage := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [fieldMemory 8 (by decide)]; exact atStage
    · rw [fieldMemory 24 (by decide)]; exact atArray
    · rw [fieldMemory 48 (by decide)]; exact atPointer
    · rw [fieldMemory 56 (by decide)]; exact atLength
    · intro one
      obtain ⟨nibs,n,atNibs,atCount⟩ := extension one
      exact ⟨nibs,n,(fieldMemory 64 (by decide)).trans atNibs,(fieldMemory 72 (by decide)).trans atCount⟩
    · intro two
      obtain ⟨node,atNode,atIndex,atOccupied⟩ := branch two
      exact ⟨node,(fieldMemory 16 (by decide)).trans atNode,(fieldMemory 32 (by decide)).trans atIndex,
        (fieldMemory 40 (by decide)).trans atOccupied⟩
  have tablePost := RlpSliceInputPrefix.after_memory_above s post array count input inputLength table
    (by have bound := heap.isLt; omega) domain (by
      intro watched lower
      apply memory
      intro same
      have sameNat := congrArg BitVec.toNat same
      omega)
  exact ⟨array,count,stage,heap,kind,fieldsPost,tablePost,above,extent,by rw [globals]; exact heapGlobal,capped,aligned⟩

#print axioms DecoderPushedTable.after_link
end InitECandidate.Runtime
