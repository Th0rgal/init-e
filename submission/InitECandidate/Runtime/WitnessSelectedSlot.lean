import InitECandidate.Runtime.WitnessPhysicalRecord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Required when mode2 selects a child; after a parent pop mode0 need not
retain this relation to the newly exposed record. -/
def WitnessSelectedSlot {F : Type} (s : PanSemStateFiniteExact 64 F) (record : BitVec 64) : Prop :=
  (s.memory (record+8)=.word (1#64) ∧ s.locals.lookup (ofString "slot")=some (.val (.word (1#64)))) ∨
  (s.memory (record+8)=.word (2#64) ∧ ∃ index : BitVec 64,
    s.memory (record+32)=.word index ∧ s.locals.lookup (ofString "slot")=some (.val (.word index)) ∧ index.toNat<16)

/-- The physical saved slice registry plus the live selector supplies the
actual next readable slice and its original input containment. -/
theorem witness_selected_physical_record_slice {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record previous input inputLength frontier : BitVec 64) (floor : Nat)
    (physical : WitnessPhysicalRecord s record previous input inputLength frontier floor)
    (selected : WitnessSelectedSlot s record) :
    ∃ array slot pointer length : BitVec 64,
      s.memory (record+24)=.word array ∧ s.memaddrs (record+24) ∧
      s.locals.lookup (ofString "slot")=some (.val (.word slot)) ∧ slot.toNat<17 ∧
      RlpSliceInputEntry s array slot pointer length input inputLength ∧ length.toNat≤inputLength.toNat := by
  obtain ⟨positive,recordEnd,domain,prev,array,count,stage,p,n,kind,stageCell,arrayCell,pCell,nCell,
    recordBefore,tableEnd,table,nibs,branch⟩ := physical
  have arrayDomain : s.memaddrs (record+24) := domain 24 (by decide)
  rcases selected with ⟨stageOne,slotOne⟩ | ⟨stageTwo,index,indexCell,slotIndex,indexBound⟩
  · have stageEq : stage=1#64 := HolWordLab.word.inj (stageCell.symm.trans stageOne)
    have countEq : count=2#64 := by
      rcases kind with ⟨_,countEq⟩ | ⟨bad,_⟩
      · exact countEq
      · rw [stageEq] at bad;cases bad
    subst count
    obtain ⟨pointer,length,entry⟩ := table (1#64) (by decide)
    exact ⟨array,1,pointer,length,arrayCell,arrayDomain,slotOne,by decide,entry,
      entry.length_bound s array 1 pointer length input inputLength⟩
  · have stageEq : stage=2#64 := HolWordLab.word.inj (stageCell.symm.trans stageTwo)
    have countEq : count=17#64 := by
      rcases kind with ⟨bad,_⟩ | ⟨_,countEq⟩
      · rw [stageEq] at bad;cases bad
      · exact countEq
    subst count
    obtain ⟨pointer,length,entry⟩ := table index (by change index.toNat<17;omega)
    exact ⟨array,index,pointer,length,arrayCell,arrayDomain,slotIndex,by omega,entry,
      entry.length_bound s array index pointer length input inputLength⟩
#print axioms witness_selected_physical_record_slice
end InitECandidate.Runtime
