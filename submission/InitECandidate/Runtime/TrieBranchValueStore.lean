import InitECandidate.Runtime.TrieNodeMetadataStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Branch value fields at offsets 160 and 168 are disjoint from all
traversal fields. Their stored values need no live-child restriction. -/
theorem TrieWalkRegistry.write_branch_value {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (parent value : BitVec 64) (registeredParent : parent ∈ branches)
    (offset : Nat) (large : 160 ≤ offset) (small : offset < 176) :
    TrieWalkRegistry live extensions branches (sourceWriteWord state (parent + BitVec.ofNat 64 offset) value) := by
  have member := layout.branchLive registeredParent
  have capacity := layout.branchSize parent registeredParent
  have separate (node : BitVec 64) (registered : node ∈ live) (field : Nat)
      (inside : field < size node) (different : field ≠ offset) :
      node + BitVec.ofNat 64 field ≠ parent + BitVec.ofNat 64 offset :=
    layout.fields_ne node parent registered member field offset inside (by omega) (Or.inr different)
  have kindSeparate (node : BitVec 64) (registered : node ∈ live) :
      node ≠ parent + BitVec.ofNat 64 offset := by
    simpa using separate node registered 0 (layout.positive node registered) (by omega)
  have extensionSeparate (node : BitVec 64) (registered : node ∈ extensions) (field : Nat)
      (lower : 32 ≤ field) (upper : field < 56) :
      node + BitVec.ofNat 64 field ≠ parent + BitVec.ofNat 64 offset :=
    separate node (layout.extensionLive registered) field
      (by have record := layout.extensionSize node registered; omega) (by omega)
  constructor
  · intro node registered child empty loaded
    have lengthSeparate := extensionSeparate node registered 40 (by decide) (by decide)
    have childSeparate := extensionSeparate node registered 48 (by decide) (by decide)
    apply registry.order node registered child
    · simpa [sourceWriteWord,lengthSeparate] using empty
    · simpa [sourceWriteWord,childSeparate] using loaded
  · intro node registered child loaded
    apply registry.extensionChildren node registered child
    simpa [sourceWriteWord,extensionSeparate node registered 48 (by decide) (by decide)] using loaded
  · intro node registered slot slotSmall child loaded
    have address : branchChildAddress node slot = node + BitVec.ofNat 64 (32 + slot * 8) := by
      simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
    have childSeparate : branchChildAddress node slot ≠ parent + BitVec.ofNat 64 offset := by
      rw [address]
      apply separate node (layout.branchLive registered) (32 + slot * 8)
      · have record := layout.branchSize node registered
        omega
      · omega
    apply registry.branchChildren node registered slot slotSmall child
    simpa [sourceWriteWord,childSeparate] using loaded
  · intro node registered loaded
    apply registry.extensionKind node registered
    simpa [sourceWriteWord,kindSeparate node registered] using loaded
  · intro node registered kind loaded nonzero nonleaf nonext
    apply registry.branchKind node registered kind _ nonzero nonleaf nonext
    simpa [sourceWriteWord,kindSeparate node registered] using loaded

#print axioms TrieWalkRegistry.write_branch_value
end InitECandidate.Runtime
