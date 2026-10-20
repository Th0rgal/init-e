import InitECandidate.Runtime.TriePayloadWords
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The actual old-memory frame below the heap frontier preserves every old
payload field; record extents supply the physical address inequalities. -/
theorem TriePayloadWords.after_below_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64}
 (valid : TriePayloadWords s live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (memory : ∀address : BitVec 64,address.toNat<frontier.toNat→post.memory address=s.memory address) :
 TriePayloadWords post live extensions branches := by
 have field (node : BitVec 64) (member : node∈live) (offset : Nat) (small : offset<size node) :
  post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  apply memory
  rw [world.layout.field_nat node member offset small]
  have allocated:=world.allocated node member
  omega
 constructor
 · intro node member nonExt nonBranch
   have capacity:=paths.leafCapacity node member nonExt nonBranch
   obtain ⟨⟨value,valueAt⟩,⟨length,lengthAt⟩⟩:=valid.leaf node member nonExt nonBranch
   exact ⟨⟨value,(field node member 48 (by omega)).trans valueAt⟩,
    ⟨length,(field node member 56 (by omega)).trans lengthAt⟩⟩
 · intro node member
   have capacity:=world.layout.branchSize node member
   have registered:=world.layout.branchLive member
   obtain ⟨⟨value,valueAt⟩,⟨length,lengthAt⟩⟩:=valid.branch node member
   exact ⟨⟨value,(field node registered 160 (by omega)).trans valueAt⟩,
    ⟨length,(field node registered 168 (by omega)).trans lengthAt⟩⟩

#print axioms TriePayloadWords.after_below_frame
end InitECandidate.Runtime
