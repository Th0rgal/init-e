import InitECandidate.Runtime.NodeNewBranchTraversalRegistry
import InitECandidate.Runtime.TrieNodeLayoutAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual branch construction extends both the traversal registry and the
allocated-record layout, carrying the updated frontier to later constructors. -/
theorem evaluate_nodeNewBranch_layout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (pointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 179 ≤ state.clock)
    (aligned : pointer.toNat % 8 = 0) (budget : pointer.toNat + 176 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (registry : TrieWalkRegistry live extensions branches state)
    (layout : TrieNodeLayout live extensions branches size)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ pointer.toNat) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_branch") []) = (none,ready) ∧
      state.clock ≤ ready.clock + 179 ∧ ready.clock ≤ state.clock ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 176))) ∧
      TrieWalkRegistry (insert pointer live) extensions (insert pointer branches) ready ∧
      TrieNodeLayout (insert pointer live) extensions (insert pointer branches) (trieRecordSizeInsert size pointer 176) ∧
      (∀ node ∈ insert pointer live,
        node.toNat + trieRecordSizeInsert size pointer 176 node ≤ (allocationEnd pointer 176).toNat) := by
  have liveBefore : ∀ node ∈ live, node.toNat < pointer.toNat := by
    intro node member
    have nonempty := layout.positive node member
    have endBound := frontier node member
    omega
  have headers : ∀ node ∈ extensions, node.toNat + 56 ≤ pointer.toNat := by
    intro node member
    have record := layout.extensionSize node member
    have endBound := frontier node (layout.extensionLive member)
    omega
  have branchHeaders : ∀ node ∈ branches, node.toNat + 176 ≤ pointer.toNat := by
    intro node member
    have record := layout.branchSize node member
    have endBound := frontier node (layout.branchLive member)
    omega
  obtain ⟨ready,run,cost,remaining,locals,heapNext,registered,_⟩ := evaluate_nodeNewBranch_traversal_registry
    state live extensions branches pointer heap code ticks aligned budget heapDomain liveBefore headers branchHeaders registry
  have allocated := layout.allocate pointer 176 (by decide) (by omega) frontier
  have fresh : pointer ∉ live := by intro member; have before := liveBefore pointer member; omega
  have notExtension : pointer ∉ extensions := fun member => fresh (layout.extensionLive member)
  have classified := allocated.register_branch pointer (Set.mem_insert _ _) (by simp [trieRecordSizeInsert]) notExtension
  have covers := (allocationEnd_covers pointer 176 (by exact budget)).1
  change pointer.toNat + 176 ≤ (allocationEnd pointer 176).toNat at covers
  exact ⟨ready,run,cost,remaining,locals,heapNext,registered,classified,
    layout.allocate_frontier pointer 176 (allocationEnd pointer 176).toNat frontier covers⟩

#print axioms evaluate_nodeNewBranch_layout
end InitECandidate.Runtime
