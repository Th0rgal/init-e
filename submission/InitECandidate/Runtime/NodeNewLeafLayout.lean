import InitECandidate.Runtime.NodeNewLeafTraversalRegistry
import InitECandidate.Runtime.TrieNodeLayoutAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual leaf construction extends both the traversal registry and the
allocated-record layout, carrying the updated frontier to later constructors. -/
theorem evaluate_nodeNewLeaf_layout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (nibArgument sizeArgument valueArgument lengthArgument : ExpHOL 64)
    (pointer nib nlen vptr vlen : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [nibArgument,sizeArgument,valueArgument,lengthArgument] = some [.val (.word nib),.val (.word nlen),.val (.word vptr),.val (.word vlen)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (budget : pointer.toNat + 64 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (registry : TrieWalkRegistry live extensions branches state)
    (layout : TrieNodeLayout live extensions branches size)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ pointer.toNat) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_leaf") [nibArgument,sizeArgument,valueArgument,lengthArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 64))) ∧
      TrieWalkRegistry (insert pointer live) extensions branches ready ∧
      TrieNodeLayout (insert pointer live) extensions branches (trieRecordSizeInsert size pointer 64) ∧
      (∀ node ∈ insert pointer live,
        node.toNat + trieRecordSizeInsert size pointer 64 node ≤ (allocationEnd pointer 64).toNat) := by
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
  obtain ⟨ready,run,clock,locals,heapNext,registered,_⟩ := evaluate_nodeNewLeaf_traversal_registry
    state live extensions branches nibArgument sizeArgument valueArgument lengthArgument pointer nib nlen vptr vlen args heap code ticks budget heapDomain liveBefore headers branchHeaders registry
  have allocated := layout.allocate pointer 64 (by decide) (by omega) frontier
  have fresh : pointer ∉ live := by intro member; have before := liveBefore pointer member; omega
  have classified := allocated
  have covers := (allocationEnd_covers pointer 64 (by exact budget)).1
  change pointer.toNat + 64 ≤ (allocationEnd pointer 64).toNat at covers
  exact ⟨ready,run,clock,locals,heapNext,registered,classified,
    layout.allocate_frontier pointer 64 (allocationEnd pointer 64).toNat frontier covers⟩

#print axioms evaluate_nodeNewLeaf_layout
end InitECandidate.Runtime
