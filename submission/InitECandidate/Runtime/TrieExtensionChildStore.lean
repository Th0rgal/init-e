import InitECandidate.Runtime.TrieNodeMetadataStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Updating a positive-length extension can select any live/null child.
Its segment guarantees progress, so the child need not have a smaller address. -/
theorem TrieWalkRegistry.write_extension_child {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (parent child length : BitVec 64) (registered : parent ∈ extensions)
    (segment : state.memory (parent + BitVec.ofNat 64 40) = .word length) (positive : length ≠ 0)
    (childValid : child = 0 ∨ child ∈ live) :
    TrieWalkRegistry live extensions branches (sourceWriteWord state (parent + BitVec.ofNat 64 48) child) := by
  have parentLive := layout.extensionLive registered
  have capacity := layout.extensionSize parent registered
  have kinds : ∀ node ∈ live, node ≠ parent + BitVec.ofNat 64 48 := by
    intro node member
    simpa using layout.fields_ne node parent member parentLive 0 48
      (layout.positive node member) (by omega) (Or.inr (by decide))
  have lengths : ∀ node ∈ extensions, node + BitVec.ofNat 64 40 ≠ parent + BitVec.ofNat 64 48 := by
    intro node member
    exact layout.fields_ne node parent (layout.extensionLive member) parentLive 40 48
      (by have bound := layout.extensionSize node member; omega) (by omega) (Or.inr (by decide))
  apply registry.write_child state live extensions branches _ child childValid kinds lengths
  intro node member same empty
  by_cases identical : node = parent
  · subst node
    have zero : length = 0 := HolWordLab.word.inj (segment.symm.trans empty)
    exact False.elim (positive zero)
  · have separate := layout.fields_separate node parent (layout.extensionLive member) parentLive identical 48 48
      (by have bound := layout.extensionSize node member; omega) (by omega)
    exact False.elim (separate same)

/-- An insertion backlink identifies a branch child slot or a positive-length
extension child field. Root-result assignment uses a separate source path. -/
def TrieChildSlot {F : Type} (state : PanSemStateFiniteExact 64 F)
    (extensions branches : Set (BitVec 64)) (address : BitVec 64) : Prop :=
  (∃ parent ∈ branches, ∃ slot : Nat, slot < 16 ∧ address = branchChildAddress parent slot) ∨
  (∃ parent ∈ extensions, ∃ length : BitVec 64,
    address = parent + BitVec.ofNat 64 48 ∧ state.memory (parent + BitVec.ofNat 64 40) = .word length ∧ length ≠ 0)

theorem TrieWalkRegistry.write_slot {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (address child : BitVec 64) (slot : TrieChildSlot state extensions branches address)
    (childValid : child = 0 ∨ child ∈ live) :
    TrieWalkRegistry live extensions branches (sourceWriteWord state address child) := by
  rcases slot with ⟨parent,member,index,small,rfl⟩ | ⟨parent,member,length,rfl,segment,positive⟩
  · exact registry.write_branch_slot state live extensions branches size layout parent child member index small childValid
  · exact registry.write_extension_child state live extensions branches size layout parent child length member segment positive childValid

#print axioms TrieWalkRegistry.write_extension_child
#print axioms TrieWalkRegistry.write_slot
end InitECandidate.Runtime
