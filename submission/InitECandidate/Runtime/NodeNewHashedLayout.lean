import InitECandidate.Runtime.NodeNewHashedTraversalRegistry
import InitECandidate.Runtime.TrieNodeLayoutAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual hashed construction extends both the traversal registry and the
allocated-record layout, carrying the updated frontier to later constructors. -/
theorem evaluate_nodeNewHashed_layout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (argument : ExpHOL 64)
    (pointer hash : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word hash)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (budget : pointer.toNat + 32 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (registry : TrieWalkRegistry live extensions branches state)
    (layout : TrieNodeLayout live extensions branches size)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ pointer.toNat) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_hashed") [argument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 32))) ∧
      TrieWalkRegistry (insert pointer live) extensions branches ready ∧
      TrieNodeLayout (insert pointer live) extensions branches (trieRecordSizeInsert size pointer 32) ∧
      (∀ node ∈ insert pointer live,
        node.toNat + trieRecordSizeInsert size pointer 32 node ≤ (allocationEnd pointer 32).toNat) := by
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
  obtain ⟨ready,run,clock,locals,heapNext,registered,_⟩ := evaluate_nodeNewHashed_traversal_registry
    state live extensions branches argument pointer hash args heap code ticks budget heapDomain liveBefore headers branchHeaders registry
  have allocated := layout.allocate pointer 32 (by decide) (by omega) frontier
  have fresh : pointer ∉ live := by intro member; have before := liveBefore pointer member; omega
  have classified := allocated
  have covers := (allocationEnd_covers pointer 32 (by exact budget)).1
  change pointer.toNat + 32 ≤ (allocationEnd pointer 32).toNat at covers
  exact ⟨ready,run,clock,locals,heapNext,registered,classified,
    layout.allocate_frontier pointer 32 (allocationEnd pointer 32).toNat frontier covers⟩

#print axioms evaluate_nodeNewHashed_layout
end InitECandidate.Runtime
