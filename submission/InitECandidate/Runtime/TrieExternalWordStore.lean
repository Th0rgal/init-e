import InitECandidate.Runtime.TrieNodePathsContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An external table-header cell is before all records and separate from
the actual containing cells of every stored path. Both are current-state
geometry facts; neither assumes a future memory frame. -/
def TrieExternalWord {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live branches : Set (BitVec 64)) (address : BitVec 64) : Prop :=
 (∀node∈live,address.toNat<node.toNat) ∧
 (∀node∈live,node∉branches→∀key len : BitVec 64,
  s.memory (node+32)=.word key→s.memory (node+40)=.word len→
  ∀offset : Nat,offset<len.toNat→panByteAlignHOL (key+BitVec.ofNat 64 offset)≠address)

/-- A concrete external header store preserves the allocated trie and all
actual stored paths. Separation of the stored key bytes is explicit. -/
theorem TrieExternalWord.write_world_paths {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier address : BitVec 64}
 (external : TrieExternalWord s live branches address)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier) (value : BitVec 64) :
 AllocatedTrieWorld (sourceWriteWord s address value) live extensions branches size frontier ∧
 TrieNodeKinds (sourceWriteWord s address value) live extensions branches ∧
 TrieNodePaths (sourceWriteWord s address value) live extensions branches size frontier := by
 have fieldSeparate (node : BitVec 64) (member : node∈live) (offset : Nat) (inside : offset<size node) :
  node+BitVec.ofNat 64 offset≠address := by
  intro equal
  have natural:=congrArg BitVec.toNat equal
  rw [world.layout.field_nat node member offset inside] at natural
  have:=external.1 node member
  omega
 have registryFrame (watched : BitVec 64) (owned : TrieWalkRegistryWord live extensions branches watched) :
  (sourceWriteWord s address value).memory watched=s.memory watched := by
  have separate : watched≠address := by
   rcases owned with ⟨node,member,rfl⟩ | ⟨node,member,rfl|rfl⟩ | ⟨node,member,index,small,rfl⟩
   · simpa using fieldSeparate watched member 0 (world.layout.positive watched member)
   · exact fieldSeparate node (world.layout.extensionLive member) 40 (by have:=world.layout.extensionSize node member;omega)
   · exact fieldSeparate node (world.layout.extensionLive member) 48 (by have:=world.layout.extensionSize node member;omega)
   · have actual : branchChildAddress node index=node+BitVec.ofNat 64 (32+index*8) := by
      simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
     rw [actual]
     exact fieldSeparate node (world.layout.branchLive member) (32+index*8) (by have:=world.layout.branchSize node member;omega)
  simp [sourceWriteWord,separate]
 refine ⟨⟨world.registry.after_word_frame registryFrame,world.positive.after_registry_word_frame registryFrame,
  world.layout,world.allocated,world.heap,world.capped,world.aligned⟩,?_,?_⟩
 · exact kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive
    (fun node member=>registryFrame node (Or.inl ⟨node,member,rfl⟩))
 · refine ⟨paths.leafCapacity,?_⟩
   intro node member nonBranch
   obtain ⟨key,len,keyAt,lenAt,short,path⟩:=paths.paths node member nonBranch
   have capacity:=paths.header_capacity world.layout node member nonBranch
   have keyAtTyped : s.memory (node+32#64)=.word key:=keyAt
   have lenAtTyped : s.memory (node+40#64)=.word len:=lenAt
   refine ⟨key,len,?_,?_,short,path.nibbles.after_word_outside address value
    (external.2 node member nonBranch key len keyAt lenAt),path.extent,path.separate⟩
   · simp [sourceWriteWord,fieldSeparate node member 32 (by omega),keyAtTyped]
   · simp [sourceWriteWord,fieldSeparate node member 40 (by omega),lenAtTyped]

#print axioms TrieExternalWord.write_world_paths
end InitECandidate.Runtime
