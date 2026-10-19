import InitECandidate.Runtime.DecodeStepPendingTableMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem DecoderPushedTable.enlarge_input {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength outer outerLength : BitVec 64) (ceiling : Nat)
    (valid : DecoderPushedTable s record pointer length input inputLength ceiling)
    (starts : outer.toNat ≤ input.toNat)
    (ends : input.toNat+inputLength.toNat ≤ outer.toNat+outerLength.toNat) :
    DecoderPushedTable s record pointer length outer outerLength ceiling := by
  obtain ⟨array,count,stage,heap,kind,fields,table,above,extent,heapGlobal,capped,aligned⟩ := valid
  refine ⟨array,count,stage,heap,kind,fields,?_,above,extent,heapGlobal,capped,aligned⟩
  intro index inside
  obtain ⟨p,n,entry⟩ := table index inside
  exact ⟨p,n,entry.readable,starts.trans entry.startsWithin,entry.endsWithin.trans ends,entry.noWrap⟩

#print axioms DecoderPushedTable.enlarge_input
end InitECandidate.Runtime
