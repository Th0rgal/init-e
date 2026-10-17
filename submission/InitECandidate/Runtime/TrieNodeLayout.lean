import InitECandidate.Runtime.TrieWalkRegistryChildStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Allocated trie records occupy disjoint natural intervals; capacities
reflect the actual constructor sizes. Extension and branch records differ. -/
structure TrieNodeLayout (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) : Prop where
  positive : ∀ node ∈ live, 0 < size node
  bounded : ∀ node ∈ live, node.toNat + size node ≤ 2^64
  separate : ∀ node ∈ live, ∀ other ∈ live, node ≠ other →
    node.toNat + size node ≤ other.toNat ∨ other.toNat + size other ≤ node.toNat
  extensionLive : extensions ⊆ live
  branchLive : branches ⊆ live
  extensionSize : ∀ node ∈ extensions, 56 ≤ size node
  branchSize : ∀ node ∈ branches, 176 ≤ size node
  differentKinds : Disjoint extensions branches

/-- Every field address inside an allocated record has its natural value. -/
theorem TrieNodeLayout.field_nat {live extensions branches : Set (BitVec 64)}
    {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
    (node : BitVec 64) (member : node ∈ live) (offset : Nat) (inside : offset < size node) :
    (node + BitVec.ofNat 64 offset).toNat = node.toNat + offset := by
  have bound := layout.bounded node member
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

/-- Fields of distinct disjoint records cannot alias. -/
theorem TrieNodeLayout.fields_separate {live extensions branches : Set (BitVec 64)}
    {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
    (node other : BitVec 64) (member : node ∈ live) (otherMember : other ∈ live)
    (different : node ≠ other) (offset otherOffset : Nat)
    (inside : offset < size node) (otherInside : otherOffset < size other) :
    node + BitVec.ofNat 64 offset ≠ other + BitVec.ofNat 64 otherOffset := by
  intro equal
  have same := congrArg BitVec.toNat equal
  rw [layout.field_nat node member offset inside,layout.field_nat other otherMember otherOffset otherInside] at same
  have intervals := layout.separate node member other otherMember different
  rcases intervals with before | after <;> omega

/-- A branch child slot cannot alias any live kind cell or any extension
length/child cell. These are exactly the child-store registry premises. -/
theorem TrieNodeLayout.branch_slot_separate {live extensions branches : Set (BitVec 64)}
    {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
    (parent : BitVec 64) (registered : parent ∈ branches) (slot : Nat) (small : slot < 16) :
    (∀ node ∈ live, node ≠ branchChildAddress parent slot) ∧
    (∀ node ∈ extensions, node + BitVec.ofNat 64 40 ≠ branchChildAddress parent slot) ∧
    (∀ node ∈ extensions, node + BitVec.ofNat 64 48 ≠ branchChildAddress parent slot) := by
  have parentLive := layout.branchLive registered
  have capacity := layout.branchSize parent registered
  have inside : 32 + slot * 8 < size parent := by omega
  have address : branchChildAddress parent slot = parent + BitVec.ofNat 64 (32 + slot * 8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
  constructor
  · intro node member
    rw [address]
    by_cases same : node = parent
    · subst node
      intro equal
      have natural := layout.field_nat parent parentLive (32 + slot * 8) inside
      have sameNat := congrArg BitVec.toNat equal
      rw [natural] at sameNat
      omega
    · simpa using layout.fields_separate node parent member parentLive same 0 (32 + slot * 8)
        (layout.positive node member) inside
  · have extensionFields (offset : Nat) (bound : offset < 56) :
        ∀ node ∈ extensions, node + BitVec.ofNat 64 offset ≠ branchChildAddress parent slot := by
      intro node member
      have different : node ≠ parent := by
        intro same
        subst node
        exact Set.disjoint_left.mp layout.differentKinds member registered
      rw [address]
      exact layout.fields_separate node parent (layout.extensionLive member) parentLive different
        offset (32 + slot * 8) (by have record := layout.extensionSize node member; omega) inside
    exact ⟨extensionFields 40 (by decide),extensionFields 48 (by decide)⟩

/-- A live/null branch child update preserves the registry from allocated
record separation, without any assumption ordering branch children. -/
theorem TrieWalkRegistry.write_branch_slot {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (parent child : BitVec 64) (registered : parent ∈ branches) (slot : Nat) (small : slot < 16)
    (childValid : child = 0 ∨ child ∈ live) :
    TrieWalkRegistry live extensions branches (sourceWriteWord state (branchChildAddress parent slot) child) := by
  obtain ⟨kinds,lengths,children⟩ := layout.branch_slot_separate parent registered slot small
  apply registry.write_child state live extensions branches _ child childValid kinds lengths
  intro node member same _
  exact False.elim (children node member same)

#print axioms TrieNodeLayout.field_nat
#print axioms TrieNodeLayout.fields_separate
#print axioms TrieNodeLayout.branch_slot_separate
#print axioms TrieWalkRegistry.write_branch_slot
end InitECandidate.Runtime
