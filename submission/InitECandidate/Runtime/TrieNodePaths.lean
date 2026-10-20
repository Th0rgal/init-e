import InitECandidate.Runtime.FreshTriePathBuffers
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Indexed leaves and extensions carry actual stored key/length words.
Their path slices are at most eighteen nibbles and their containing byte
cells are separate from every node record. Branches have no segment header. -/
structure TrieNodePaths {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64) : Prop where
 leafCapacity : ∀node∈live,node∉extensions→node∉branches→64≤size node
 paths : ∀node∈live,node∉branches→∃key length : BitVec 64,
  s.memory (node+32)=.word key ∧s.memory (node+40)=.word length ∧length.toNat≤18 ∧
  TriePathBuffer s live size key length frontier

theorem TrieNodePaths.empty {F : Type} (s : PanSemStateFiniteExact 64 F)
 (size : BitVec 64 → Nat) (frontier : BitVec 64) : TrieNodePaths s ∅ ∅ ∅ size frontier := by
 constructor <;> intro node member <;> exact False.elim member

/-- Both real segment-header words fit in the allocated record. Exact kinds
and constructor sizes distinguish the leaf and extension cases. -/
theorem TrieNodePaths.header_capacity {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (paths : TrieNodePaths s live extensions branches size frontier)
 (layout : TrieNodeLayout live extensions branches size)
 (node : BitVec 64) (member : node∈live) (nonBranch : node∉branches) : 48≤size node := by
 classical
 by_cases extension : node∈extensions
 · have:=layout.extensionSize node extension;omega
 · have:=paths.leafCapacity node member extension nonBranch;omega

#print axioms TrieNodePaths.empty
#print axioms TrieNodePaths.header_capacity
end InitECandidate.Runtime
