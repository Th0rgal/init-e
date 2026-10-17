import InitECandidate.Runtime.TrieWalkRegistry
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Fresh allocation writes preserve all sixteen child slots of every
complete branch record below the allocation frontier. -/
theorem branchChildrenIn_before_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (live branches : Set (BitVec 64)) (pointer : BitVec 64)
    (children : BranchChildrenIn live branches state)
    (headers : ∀ node ∈ branches, node.toNat + 176 ≤ pointer.toNat)
    (frame : ∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) :
    BranchChildrenIn live branches post := by
  intro node member slot small child loaded
  have bound := headers node member
  have limit := pointer.isLt
  have literal : (BitVec.ofNat 64 slot).toNat = slot := Nat.mod_eq_of_lt (by omega)
  have scaled : (BitVec.ofNat 64 slot * (8 : BitVec 64)).toNat = slot * 8 := by
    rw [BitVec.toNat_mul,literal]
    change (slot * 8) % 18446744073709551616 = slot * 8
    omega
  have base : (node + (32 : BitVec 64)).toNat = node.toNat + 32 := by
    rw [BitVec.toNat_add_of_lt (by change node.toNat + 32 < 2^64; omega)]
    rfl
  have natural : (branchChildAddress node slot).toNat = node.toNat + 32 + slot * 8 := by
    unfold branchChildAddress
    rw [BitVec.toNat_add_of_lt (by rw [base,scaled]; omega),base,scaled]
  have before : (branchChildAddress node slot).toNat < pointer.toNat := by rw [natural]; omega
  exact children node member slot small child ((frame _ before).symm.trans loaded)

/-- Allocation beyond complete old records preserves the entire traversal
registry, including classification of all previously live nodes. -/
theorem TrieWalkRegistry.before_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (pointer : BitVec 64)
    (registry : TrieWalkRegistry live extensions branches state)
    (liveBefore : ∀ node ∈ live, node.toNat < pointer.toNat)
    (extensionHeaders : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat)
    (branchHeaders : ∀ node ∈ branches, node.toNat + 176 ≤ pointer.toNat)
    (frame : ∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) :
    TrieWalkRegistry live extensions branches post := by
  constructor
  · exact extensionOrderFamily_before_frame state post extensions pointer registry.order extensionHeaders frame
  · exact extensionChildrenIn_before_frame state post live extensions pointer registry.extensionChildren extensionHeaders frame
  · exact branchChildrenIn_before_frame state post live branches pointer registry.branchChildren branchHeaders frame
  · intro node member loaded
    rw [frame node (liveBefore node member)] at loaded
    exact registry.extensionKind node member loaded
  · intro node member kind loaded nonzero nonleaf nonext
    rw [frame node (liveBefore node member)] at loaded
    exact registry.branchKind node member kind loaded nonzero nonleaf nonext

#print axioms branchChildrenIn_before_frame
#print axioms TrieWalkRegistry.before_frame
end InitECandidate.Runtime
