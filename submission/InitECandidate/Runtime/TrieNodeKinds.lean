import InitECandidate.Runtime.AllocatedTrieMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Exact source node tags supplement the traversal registry, whose kind
classification is deliberately one-way. These exclude treating a leaf value
write as an extension or branch traversal-field update. -/
structure TrieNodeKinds {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) : Prop where
 leaf : ∀node∈live,node∉extensions→node∉branches→s.memory node=.word 1
 extension : ∀node∈extensions,s.memory node=.word 2
 branch : ∀node∈branches,s.memory node=.word 3

theorem TrieNodeKinds.empty {F : Type} (s : PanSemStateFiniteExact 64 F) : TrieNodeKinds s ∅ ∅ ∅ := by
 constructor <;> intro node member <;> exact False.elim member

theorem TrieNodeKinds.after_kind_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} (kinds : TrieNodeKinds s live extensions branches)
 (extensionLive : extensions⊆live) (branchLive : branches⊆live)
 (frame : ∀node∈live,post.memory node=s.memory node) : TrieNodeKinds post live extensions branches := by
 constructor
 · intro node member noExtension noBranch
   rw [frame node member];exact kinds.leaf node member noExtension noBranch
 · intro node member;rw [frame node (extensionLive member)];exact kinds.extension node member
 · intro node member;rw [frame node (branchLive member)];exact kinds.branch node member

theorem TrieNodeKinds.leaf_separate {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} (kinds : TrieNodeKinds s live extensions branches)
 (node : BitVec 64) (tag : s.memory node=.word (1#64)) : node∉extensions ∧node∉branches := by
 constructor
 · intro member
   have impossible : (2#64)=(1#64):=HolWordLab.word.inj ((kinds.extension node member).symm.trans tag)
   exact (by decide : (2#64)≠(1#64)) impossible
 · intro member
   have impossible : (3#64)=(1#64):=HolWordLab.word.inj ((kinds.branch node member).symm.trans tag)
   exact (by decide : (3#64)≠(1#64)) impossible

#print axioms TrieNodeKinds.after_kind_frame
#print axioms TrieNodeKinds.leaf_separate
end InitECandidate.Runtime
