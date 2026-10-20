import InitECandidate.Runtime.TrieNodeKinds
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A concrete live/null child store preserves exact tags as well as the
allocated world. The separation hypotheses are actual record geometry. -/
theorem AllocatedTrieWorld.write_child_kinds {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches) (address child : BitVec 64)
 (childValid : child=0 ∨child∈live)
 (kindsSeparate : ∀node∈live,node≠address)
 (lengthsSeparate : ∀node∈extensions,node+40≠address) :
 AllocatedTrieWorld (sourceWriteWord s address child) live extensions branches size frontier ∧
 TrieNodeKinds (sourceWriteWord s address child) live extensions branches := by
 refine ⟨world.write_child address child childValid kindsSeparate lengthsSeparate,?_⟩
 apply kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive
 intro node registered
 simp [sourceWriteWord,kindsSeparate node registered]

/-- Branch child links use one of the sixteen actual slots; all separation
premises follow from allocated record layout rather than a caller callback. -/
theorem AllocatedTrieWorld.write_branch_child_kinds {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (parent child : BitVec 64) (member : parent∈branches) (slot : Nat) (small : slot<16)
 (childValid : child=0 ∨child∈live) :
 AllocatedTrieWorld (sourceWriteWord s (branchChildAddress parent slot) child) live extensions branches size frontier ∧
 TrieNodeKinds (sourceWriteWord s (branchChildAddress parent slot) child) live extensions branches := by
 obtain ⟨kindFrame,lengthFrame,_⟩:=world.layout.branch_slot_separate parent member slot small
 exact world.write_child_kinds kinds _ child childValid kindFrame lengthFrame

#print axioms AllocatedTrieWorld.write_child_kinds
#print axioms AllocatedTrieWorld.write_branch_child_kinds
end InitECandidate.Runtime
