import InitECandidate.Runtime.TrieWalkRegistry
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Exactly the memory words observed by the live-trie traversal registry. -/
def TrieWalkRegistryWord (live extensions branches : Set (BitVec 64)) (address : BitVec 64) : Prop :=
 (∃node∈live,address=node) ∨
 (∃node∈extensions,address=node+40 ∨address=node+48) ∨
 (∃node∈branches,∃slot : Nat,slot<16 ∧address=branchChildAddress node slot)

theorem TrieWalkRegistry.after_word_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)}
 (valid : TrieWalkRegistry live extensions branches s)
 (memory : ∀address,TrieWalkRegistryWord live extensions branches address→post.memory address=s.memory address) :
 TrieWalkRegistry live extensions branches post := by
 constructor
 · intro node member child empty loaded
   rw [memory _ (Or.inr (Or.inl ⟨node,member,Or.inl rfl⟩))] at empty
   rw [memory _ (Or.inr (Or.inl ⟨node,member,Or.inr rfl⟩))] at loaded
   exact valid.order node member child empty loaded
 · intro node member child loaded
   rw [memory _ (Or.inr (Or.inl ⟨node,member,Or.inr rfl⟩))] at loaded
   exact valid.extensionChildren node member child loaded
 · intro node member slot inside child loaded
   rw [memory _ (Or.inr (Or.inr ⟨node,member,slot,inside,rfl⟩))] at loaded
   exact valid.branchChildren node member slot inside child loaded
 · intro node member loaded
   rw [memory _ (Or.inl ⟨node,member,rfl⟩)] at loaded
   exact valid.extensionKind node member loaded
 · intro node member kind loaded nonzero nonleaf nonext
   rw [memory _ (Or.inl ⟨node,member,rfl⟩)] at loaded
   exact valid.branchKind node member kind loaded nonzero nonleaf nonext

#print axioms TrieWalkRegistry.after_word_frame
end InitECandidate.Runtime
