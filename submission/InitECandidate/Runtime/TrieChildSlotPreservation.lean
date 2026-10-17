import InitECandidate.Runtime.TrieExtensionChildStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Backlink typing depends only on membership and extension-length words. -/
theorem TrieChildSlot.after_length_frame {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {extensions branches : Set (BitVec 64)} {address : BitVec 64}
    (typed : TrieChildSlot state extensions branches address)
    (frame : ∀ node ∈ extensions,
      post.memory (node + BitVec.ofNat 64 40) = state.memory (node + BitVec.ofNat 64 40)) :
    TrieChildSlot post extensions branches address := by
  rcases typed with branch | ⟨parent,member,length,location,segment,positive⟩
  · exact Or.inl branch
  · exact Or.inr ⟨parent,member,length,location,(frame parent member).trans segment,positive⟩

theorem TrieChildSlot.mono {F : Type} {state : PanSemStateFiniteExact 64 F}
    {extensions largerExtensions branches largerBranches : Set (BitVec 64)} {address : BitVec 64}
    (typed : TrieChildSlot state extensions branches address)
    (includeExtensions : extensions ⊆ largerExtensions) (includeBranches : branches ⊆ largerBranches) :
    TrieChildSlot state largerExtensions largerBranches address := by
  rcases typed with ⟨parent,member,index,small,location⟩ | ⟨parent,member,length,location,segment,positive⟩
  · exact Or.inl ⟨parent,includeBranches member,index,small,location⟩
  · exact Or.inr ⟨parent,includeExtensions member,length,location,segment,positive⟩

/-- Every well-typed child slot is separate from all extension-length fields. -/
theorem TrieChildSlot.length_separate {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size) (address : BitVec 64)
    (typed : TrieChildSlot state extensions branches address) :
    ∀ node ∈ extensions, node + BitVec.ofNat 64 40 ≠ address := by
  rcases typed with ⟨parent,member,index,small,rfl⟩ | ⟨parent,member,length,rfl,_,_⟩
  · exact (layout.branch_slot_separate parent member index small).2.1
  · intro node registered
    exact layout.fields_ne node parent (layout.extensionLive registered) (layout.extensionLive member) 40 48
      (by have bound := layout.extensionSize node registered; omega)
      (by have bound := layout.extensionSize parent member; omega) (Or.inr (by decide))

/-- Committing one child backlink preserves every previously prepared backlink,
including another pointer into the same extension or branch record. -/
theorem TrieChildSlot.after_slot_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size) (address watched value : BitVec 64)
    (stored : TrieChildSlot state extensions branches address)
    (prepared : TrieChildSlot state extensions branches watched) :
    TrieChildSlot (sourceWriteWord state address value) extensions branches watched := by
  apply prepared.after_length_frame
  intro node member
  simp [sourceWriteWord,stored.length_separate state live extensions branches size layout address node member]

/-- Allocating beyond old records preserves prepared backlinks, even when the
new constructor enlarges the node classification sets. -/
theorem TrieChildSlot.before_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (extensions largerExtensions branches largerBranches : Set (BitVec 64)) (address pointer : BitVec 64)
    (typed : TrieChildSlot state extensions branches address)
    (headers : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat)
    (frame : ∀ current : BitVec 64, current.toNat < pointer.toNat → post.memory current = state.memory current)
    (includeExtensions : extensions ⊆ largerExtensions) (includeBranches : branches ⊆ largerBranches) :
    TrieChildSlot post largerExtensions largerBranches address := by
  apply TrieChildSlot.mono (includeExtensions := includeExtensions) (includeBranches := includeBranches)
  apply typed.after_length_frame
  intro node member
  have bound := headers node member
  have limit := pointer.isLt
  have natural : (node + BitVec.ofNat 64 40).toNat = node.toNat + 40 := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  apply frame
  rw [natural]
  omega

#print axioms TrieChildSlot.after_length_frame
#print axioms TrieChildSlot.mono
#print axioms TrieChildSlot.length_separate
#print axioms TrieChildSlot.after_slot_store
#print axioms TrieChildSlot.before_frame
end InitECandidate.Runtime
