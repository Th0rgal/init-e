import InitECandidate.Runtime.AllocatedTrieWorld
import InitECandidate.Runtime.TrieChildSlotPreservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Backlink typing survives node construction whenever the old classifications
are included in the new positive-extension world. The extension length may
change: its actual new positive length supplies the new witness. -/
theorem TrieChildSlot.after_positive_world {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {extensions branches live largerExtensions largerBranches : Set (BitVec 64)}
 {size : BitVec 64→Nat} {frontier address : BitVec 64}
 (typed : TrieChildSlot s extensions branches address)
 (world : AllocatedTrieWorld post live largerExtensions largerBranches size frontier)
 (extSub : extensions⊆largerExtensions) (branchSub : branches⊆largerBranches) :
 TrieChildSlot post largerExtensions largerBranches address := by
 rcases typed with ⟨parent,member,index,small,location⟩ | ⟨parent,member,oldLength,location,_,_⟩
 · exact Or.inl ⟨parent,branchSub member,index,small,location⟩
 · obtain ⟨length,field,positive⟩:=world.positive parent (extSub member)
   exact Or.inr ⟨parent,extSub member,length,location,field,positive⟩

#print axioms TrieChildSlot.after_positive_world
end InitECandidate.Runtime
