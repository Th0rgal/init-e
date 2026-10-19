import InitECandidate.Runtime.DecodeStepPendingTableMetadata
import InitECandidate.Runtime.DecodeStepTableInputEnclosure
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def DecoderBranchPlaced {F : Type} (s : PanSemStateFiniteExact 64 F) (record : BitVec 64) (floor : Nat) : Prop :=
  ∃ array branch heap : BitVec 64,
    s.memory (record+24)=.word array ∧ s.memory (record+16)=.word branch ∧
    floor ≤ branch.toNat ∧ array.toNat+272 ≤ branch.toNat ∧ branch.toNat+176 ≤ heap.toNat ∧ branch.toNat%8=0 ∧
    s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ heap.toNat ≤ 33806089496

def DecoderPlacedPushedTable {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength : BitVec 64) (ceiling floor : Nat) : Prop :=
  DecoderPushedTable s record pointer length input inputLength ceiling ∧
    (s.memory (record+8)=.word (2 : BitVec 64) → DecoderBranchPlaced s record floor)

theorem DecoderPlacedPushedTable.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength : BitVec 64) (ceiling floor : Nat)
    (valid : DecoderPlacedPushedTable s record pointer length input inputLength ceiling floor)
    (memory : post.memory=s.memory) (globals : post.globals=s.globals) (domain : post.memaddrs=s.memaddrs) :
    DecoderPlacedPushedTable post record pointer length input inputLength ceiling floor := by
  refine ⟨valid.1.after_frame s post record pointer length input inputLength ceiling memory globals domain,?_⟩
  intro stage
  have before : s.memory (record+8)=.word (2 : BitVec 64) := by rw [← memory]; exact stage
  obtain ⟨array,branch,heap,arrayCell,branchCell,floorBound,tableEnd,branchEnd,aligned,heapGlobal,capped⟩ := valid.2 before
  exact ⟨array,branch,heap,(congrFun memory _).trans arrayCell,(congrFun memory _).trans branchCell,
    floorBound,tableEnd,branchEnd,aligned,by rw [globals]; exact heapGlobal,capped⟩

theorem DecoderPlacedPushedTable.enlarge_input {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength outer outerLength : BitVec 64) (ceiling floor : Nat)
    (valid : DecoderPlacedPushedTable s record pointer length input inputLength ceiling floor)
    (starts : outer.toNat ≤ input.toNat)
    (ends : input.toNat+inputLength.toNat ≤ outer.toNat+outerLength.toNat) :
    DecoderPlacedPushedTable s record pointer length outer outerLength ceiling floor :=
  ⟨valid.1.enlarge_input s record pointer length input inputLength outer outerLength ceiling starts ends,valid.2⟩

#print axioms DecoderPlacedPushedTable.after_frame
#print axioms DecoderPlacedPushedTable.enlarge_input
end InitECandidate.Runtime
