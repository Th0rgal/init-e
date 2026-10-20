import InitECandidate.Runtime.WordSeparation
import InitECandidate.Runtime.TrieAllocationFloorFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Trie ownership includes every record word and every containing word cell
of each actual stored leaf/extension key buffer. Payload buffers are not included. -/
def TrieOwnedFootprint (memory : WordSep.Memory) (live branches : Set (BitVec 64))
 (size : BitVec 64→Nat) : Set (BitVec 64) :=
 {address | (∃node∈live,∃offset : Nat,offset<size node ∧address=node+BitVec.ofNat 64 offset) ∨
  (∃node∈live,node∉branches ∧∃key len : BitVec 64,
   memory (node+32)=.word key ∧memory (node+40)=.word len ∧
   ∃offset : Nat,offset<len.toNat ∧address=panByteAlignHOL (key+BitVec.ofNat 64 offset))}

/-- The reference memory freezes the owned values and the stored-key footprint. -/
def trieOwned (memory : WordSep.Memory) (live branches : Set (BitVec 64)) (size : BitVec 64→Nat) :
 WordSep.Assertion := WordSep.snapshot (TrieOwnedFootprint memory live branches size) memory

def trieScratch (memory : WordSep.Memory) (live branches : Set (BitVec 64))
 (size : BitVec 64→Nat) (scratch : Set (BitVec 64)) : WordSep.Assertion :=
 WordSep.sep (trieOwned memory live branches size) (WordSep.snapshot scratch memory)

/-- Package geometric separation once; subsequent operations supply their actual writes. -/
theorem trieScratch_initial (memory : WordSep.Memory) (live branches : Set (BitVec 64))
 (size : BitVec 64→Nat) (scratch : Set (BitVec 64))
 (separate : Disjoint (TrieOwnedFootprint memory live branches size) scratch) :
 (trieScratch memory live branches size scratch).holds memory :=
 ⟨separate,(by intro address owned;rfl),(by intro address owned;rfl)⟩

/-- Scratch contents may change. The actual write effect and the packaged
separation preserve the trie values, without claiming scratch values survive. -/
theorem trieScratch_frame {before after reference : WordSep.Memory}
 {live branches : Set (BitVec 64)} {size : BitVec 64→Nat} {scratch : Set (BitVec 64)}
 (owned : (trieScratch reference live branches size scratch).holds before)
 (effect : WordSep.WritesOnly scratch before after) :
 (trieOwned reference live branches size).holds after :=
 WordSep.frame _ effect owned.1.symm owned.2.1

/-- Ownership framing transports actual stored path facts through unrelated
operations. Address domain and byte order remain explicit context facts. -/
theorem TrieNodePaths.after_owned_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64}
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kept : (trieOwned s.memory live branches size).holds post.memory)
 (domain : post.memaddrs=s.memaddrs) (endian : post.be=s.be) :
 TrieNodePaths post live extensions branches size frontier := by
 refine ⟨paths.leafCapacity,?_⟩
 intro node member nonBranch
 obtain ⟨key,len,keyAt,lenAt,short,path⟩:=paths.paths node member nonBranch
 have header (offset : Nat) (small : offset<48) :
  post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  exact kept _ (Or.inl ⟨node,member,offset,by have:=paths.header_capacity world.layout node member nonBranch;omega,rfl⟩)
 have nibbles : TrieNibbleRange post key len := by
  apply path.nibbles.after_cells _ domain endian
  intro offset small
  exact kept _ (Or.inr ⟨node,member,nonBranch,key,len,keyAt,lenAt,offset,small,rfl⟩)
 exact ⟨key,len,(header 32 (by decide)).trans keyAt,(header 40 (by decide)).trans lenAt,
  short,nibbles,path.extent,path.separate⟩

theorem TrieAllocationFloor.after_owned_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64} {floor : Nat}
 (lower : TrieAllocationFloor s live branches floor)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kept : (trieOwned s.memory live branches size).holds post.memory) :
 TrieAllocationFloor post live branches floor := by
 refine ⟨lower.records,?_⟩
 intro node member nonBranch key len keyAt lenAt
 have header (offset : Nat) (small : offset<48) :
  post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  exact kept _ (Or.inl ⟨node,member,offset,by have:=paths.header_capacity world.layout node member nonBranch;omega,rfl⟩)
 exact lower.keys node member nonBranch key len
  ((header 32 (by decide)).symm.trans keyAt) ((header 40 (by decide)).symm.trans lenAt)

/-- Registry fields are a subset of the conservative record footprint. -/
theorem trieRegistryWord_owned {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier address : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (owned : TrieWalkRegistryWord live extensions branches address) :
 address∈TrieOwnedFootprint s.memory live branches size := by
 apply Or.inl
 rcases owned with ⟨node,member,rfl⟩|⟨node,member,rfl|rfl⟩|⟨node,member,index,small,rfl⟩
 · exact ⟨address,member,0,world.layout.positive address member,by simp⟩
 · exact ⟨node,world.layout.extensionLive member,40,by have:=world.layout.extensionSize node member;omega,rfl⟩
 · exact ⟨node,world.layout.extensionLive member,48,by have:=world.layout.extensionSize node member;omega,rfl⟩
 · refine ⟨node,world.layout.branchLive member,32+index*8,?_,?_⟩
   · have:=world.layout.branchSize node member;omega
   · simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]

theorem AllocatedTrieWorld.after_owned_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kept : (trieOwned s.memory live branches size).holds post.memory)
 (globals : post.globals=s.globals) :
 AllocatedTrieWorld post live extensions branches size frontier := by
 have frame : ∀address,TrieWalkRegistryWord live extensions branches address→post.memory address=s.memory address :=
  fun address owned=>kept address (trieRegistryWord_owned world owned)
 refine ⟨world.registry.after_word_frame frame,world.positive.after_registry_word_frame frame,
  world.layout,world.allocated,?_,world.capped,world.aligned⟩
 rw [globals];exact world.heap

theorem TrieNodeKinds.after_owned_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64}
 (kinds : TrieNodeKinds s live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kept : (trieOwned s.memory live branches size).holds post.memory) :
 TrieNodeKinds post live extensions branches :=
 kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive
  (fun node member=>kept node (trieRegistryWord_owned world (Or.inl ⟨node,member,rfl⟩)))

#print axioms AllocatedTrieWorld.after_owned_frame
#print axioms TrieNodeKinds.after_owned_frame

/-- Ownership extension is geometric: retain old records, their sizes, and
stored header values while admitting additional records and buffers. The
constructor's execution must separately establish these premises and new facts. -/
theorem trieOwnedFootprint_extend {before after : WordSep.Memory}
 {live branches larger newBranches : Set (BitVec 64)} {size newSize : BitVec 64→Nat}
 (records : live⊆larger) (sizes : ∀node∈live,size node≤newSize node)
 (nonBranches : ∀node∈live,node∉branches→node∉newBranches)
 (headers : ∀node∈live,node∉branches→
  after (node+32)=before (node+32) ∧after (node+40)=before (node+40)) :
 TrieOwnedFootprint before live branches size⊆TrieOwnedFootprint after larger newBranches newSize := by
 intro address owned
 rcases owned with ⟨node,member,offset,small,rfl⟩|⟨node,member,nonBranch,key,len,keyAt,lenAt,offset,small,rfl⟩
 · exact Or.inl ⟨node,records member,offset,Nat.lt_of_lt_of_le small (sizes node member),rfl⟩
 · exact Or.inr ⟨node,records member,nonBranches node member nonBranch,key,len,
    (headers node member nonBranch).1.trans keyAt,(headers node member nonBranch).2.trans lenAt,offset,small,rfl⟩

#print axioms trieScratch_frame
#print axioms TrieNodePaths.after_owned_frame
#print axioms TrieAllocationFloor.after_owned_frame
#print axioms trieOwnedFootprint_extend
end InitECandidate.Runtime
