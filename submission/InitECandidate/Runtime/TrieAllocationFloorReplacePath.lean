import InitECandidate.Runtime.TrieAllocationFloorFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Replacing a node's segment header preserves ownership when the actual
new pointer follows the floor. Other records are framed geometrically. -/
theorem TrieAllocationFloor.after_path_header {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 {frontier parent key : BitVec 64} {floor : Nat}
 (lower : TrieAllocationFloor s live branches floor)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (member : parent∈live) (capacity : 48≤size parent)
 (keyAt : post.memory (parent+32)=.word key) (keyAbove : floor≤key.toNat)
 (frame : ∀watched : BitVec 64,watched≠parent+32→watched≠parent+40→post.memory watched=s.memory watched) :
 TrieAllocationFloor post live branches floor := by
 refine ⟨lower.records,?_⟩
 intro node registered nonBranch actualKey len storedKey storedLen
 by_cases same : node=parent
 · subst node
   have equal : key=actualKey:=HolWordLab.word.inj (keyAt.symm.trans storedKey)
   simpa [←equal] using keyAbove
 · have headers (header : Nat) (which : header=32 ∨header=40) :
    post.memory (node+BitVec.ofNat 64 header)=s.memory (node+BitVec.ofNat 64 header) := by
    have cap:=paths.header_capacity world.layout node registered nonBranch
    apply frame
    · exact world.layout.fields_ne node parent registered member header 32
       (by rcases which with rfl|rfl <;>omega) (by omega) (Or.inl same)
    · exact world.layout.fields_ne node parent registered member header 40
       (by rcases which with rfl|rfl <;>omega) (by omega) (Or.inl same)
   apply lower.keys node registered nonBranch actualKey len
   · exact (headers 32 (Or.inl rfl)).symm.trans storedKey
   · exact (headers 40 (Or.inr rfl)).symm.trans storedLen

#print axioms TrieAllocationFloor.after_path_header
end InitECandidate.Runtime
